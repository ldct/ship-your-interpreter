"""Tests for the serialized private Lean build driver."""

import tempfile
import json
import unittest
import subprocess
from contextlib import redirect_stdout
from io import StringIO
from pathlib import Path
from unittest.mock import patch

from scripts import build_private


class BuildPrivateTests(unittest.TestCase):
    """Test graph parsing and resume-safety primitives."""

    def test_header_parser_handles_nested_comments_and_quoted_components(self) -> None:
        text = """/- outer /- nested -/ comment -/
import Vsa.Base Vsa.Sim.Code.«__divdi3» -- trailing
/- between -/
import Vsa.Other
namespace Vsa
import Vsa.TooLate
"""
        self.assertEqual(
            build_private.parse_header_imports(text),
            ("Vsa.Base", "Vsa.Sim.Code.__divdi3", "Vsa.Other"),
        )

    def test_modern_import_headers_and_comment_markers_in_strings(self) -> None:
        text = ('module\nprelude\npublic meta import A\nimport all B\n'
                'def marker := "/-"\n')
        self.assertEqual(build_private.parse_header_imports(text), ("A", "B"))

    def test_selected_module_follows_cross_library_and_package_imports(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            sources = {
                "Dc.lean": "import Dc.Main\n",
                "Dc/Main.lean": "import VsaIris.Helper\n",
                "Dc/Unrelated.lean": "import Missing.Unrelated\n",
                "VsaIris/Helper.lean": "import External.Base\n",
                ".lake/packages/external/src/External/Base.lean": "import Init\n",
            }
            for path, text in sources.items():
                source = repo / path
                source.parent.mkdir(parents=True, exist_ok=True)
                source.write_text(text)
            (repo / "lake-manifest.json").write_text(
                '{"packages": [{"type": "git", "name": "external", "subDir": "src"}]}'
            )
            modules = build_private.discover_modules(
                repo, roots=("Dc",), with_dependencies=True, module_roots_only=True
            )
            self.assertEqual(set(modules), {"Dc", "Dc.Main", "VsaIris.Helper", "External.Base"})
            external = modules["External.Base"]
            self.assertEqual(
                build_private.output_path(Path("/cache"), external),
                Path("/cache/External/Base.olean"),
            )
            self.assertEqual(
                [m.name for m in build_private.topological_order(modules)],
                ["External.Base", "VsaIris.Helper", "Dc.Main", "Dc"],
            )
            before = build_private.module_fingerprints(
                repo, build_private.topological_order(modules), "context"
            )
            external.source.write_text("import Init\ndef x := 1\n")
            after = build_private.module_fingerprints(
                repo, build_private.topological_order(modules), "context"
            )
            self.assertNotEqual(before["Dc"], after["Dc"])

    def test_modern_module_companion_objects_are_preserved(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            module = build_private.Module("A", Path("A.lean"), ())

            def run(command, **kwargs):
                staged = Path(command[7])
                staged.write_bytes(b"public")
                Path(str(staged) + ".private").write_bytes(b"private")
                Path(str(staged) + ".server").write_bytes(b"server")
                staged.with_suffix(".ir").write_bytes(b"ir")
                staged.with_suffix(".ir.sig").write_bytes(b"signature")
                return subprocess.CompletedProcess(command, 0, "", "")

            with patch.object(build_private.subprocess, "run", side_effect=run):
                build_private.compile_module(root, root, module)
            self.assertEqual((root / "A.olean.private").read_bytes(), b"private")
            self.assertEqual((root / "A.olean.server").read_bytes(), b"server")
            self.assertEqual((root / "A.ir").read_bytes(), b"ir")
            self.assertEqual((root / "A.ir.sig").read_bytes(), b"signature")

    def test_manifest_path_dependency_and_missing_package(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory) / "repo"
            repo.mkdir()
            sibling = repo.parent / "dependency"
            sibling.mkdir()
            (repo / "lake-manifest.json").write_text(
                '{"packages": [{"type": "path", "dir": "../dependency"}]}'
            )
            self.assertEqual(build_private.dependency_source_roots(repo), [sibling.resolve()])
            sibling.rmdir()
            with self.assertRaisesRegex(build_private.BuildError, "fetch first"):
                build_private.dependency_source_roots(repo)

    def test_explicit_missing_root_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            with self.assertRaisesRegex(build_private.BuildError, "no Lean sources"):
                build_private.discover_modules(Path(directory), roots=("Missing",))

    def test_missing_internal_import_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            (repo / "Dc.lean").write_text("import VsaIris.Missing\n")
            with self.assertRaisesRegex(build_private.BuildError, "unknown internal import"):
                build_private.discover_modules(repo, roots=("Dc",))

    def test_duplicate_dependency_module_is_rejected(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            (repo / "Dc.lean").write_text("import Shared\n")
            for name in ("one", "two"):
                package = repo / name
                package.mkdir()
                (package / "Shared.lean").write_text("def x := 1\n")
            (repo / "lake-manifest.json").write_text(
                '{"packages": [{"type": "path", "dir": "one"},'
                '{"type": "path", "dir": "two"}]}'
            )
            with self.assertRaisesRegex(build_private.BuildError, "ambiguous import Shared"):
                build_private.discover_modules(repo, roots=("Dc",), with_dependencies=True)

    def test_package_and_library_options_are_scoped_and_overridden(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            (repo / "lakefile.toml").write_text(
                'moreLeanArgs = ["--tstack=400000"]\n'
                '[leanOptions]\npp.universes = true\n'
                '[[lean_lib]]\nname = "Vsa"\n'
                'leanOptions.pp.universes = false\n'
                'leanOptions.backward.isDefEq.respectTransparency = false\n'
                '[[lean_lib]]\nname = "VsaIris"\n'
            )
            hooks = build_private.Module("Vsa.Sim.Hooks", Path("Vsa/Sim/Hooks.lean"), ())
            iris = build_private.Module("VsaIris.Base", Path("VsaIris/Base.lean"), ())
            self.assertEqual(build_private.configured_lean_args(repo, hooks), [
                "-Dbackward.isDefEq.respectTransparency=false",
                "-Dpp.universes=false", "--tstack=400000",
            ])
            self.assertEqual(build_private.configured_lean_args(repo, iris), [
                "-Dpp.universes=true", "--tstack=400000",
            ])

    def test_dependency_uses_own_config_and_config_changes_invalidate_importers(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            dependency = repo / "package"
            dependency.mkdir()
            source = dependency / "External.lean"
            source.write_text("def x := 1\n")
            (repo / "Dc.lean").write_text("import External\n")
            config = dependency / "lakefile.toml"
            config.write_text('[leanOptions]\npp.universes = true\n')
            module = build_private.Module("External", source, (), dependency)
            importer = build_private.Module("Dc", Path("Dc.lean"), ("External",))
            self.assertEqual(build_private.configured_lean_args(repo, module), ["-Dpp.universes=true"])
            before = build_private.module_fingerprints(repo, [module, importer], "same")
            config.write_text('[leanOptions]\npp.universes = false\n')
            after = build_private.module_fingerprints(repo, [module, importer], "same")
            self.assertNotEqual(before["External"], after["External"])
            self.assertNotEqual(before["Dc"], after["Dc"])

    def test_compiler_receives_configured_options(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            (repo / "lakefile.toml").write_text(
                '[[lean_lib]]\nname = "Vsa"\n'
                'leanOptions.backward.isDefEq.respectTransparency = false\n'
            )
            module = build_private.Module("Vsa.A", Path("Vsa/A.lean"), ())

            def run(command, **kwargs):
                self.assertIn("-Dbackward.isDefEq.respectTransparency=false", command[10:])
                Path(command[7]).write_bytes(b"object")
                return subprocess.CompletedProcess(command, 0, "", "")

            with patch.object(build_private.subprocess, "run", side_effect=run):
                build_private.compile_module(repo, repo / "output", module)

    def test_build_resolves_environment_once_and_refreshes_next_build(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory) / "repo with spaces"
            (repo / "Vsa").mkdir(parents=True)
            (repo / "Vsa/A.lean").write_text("def a := 1\n")
            (repo / "Vsa.lean").write_text("import Vsa.A\n")
            backend = Path(directory) / "private objects"
            resolutions = 0
            compiles = 0

            def run(command, **kwargs):
                nonlocal resolutions, compiles
                if command[:2] == ["lake", "env"]:
                    resolutions += 1
                    return subprocess.CompletedProcess(command, 0, json.dumps({
                        "PATH": "/resolved/toolchain/bin",
                        "LEAN_PATH": "/dependency path",
                        "BUILD_GENERATION": str(resolutions),
                    }), "")
                compiles += 1
                self.assertEqual(command[0], "sh")
                self.assertEqual(kwargs["env"]["PATH"], "/resolved/toolchain/bin")
                self.assertEqual(kwargs["env"]["LEAN_PATH"], "/dependency path")
                self.assertEqual(kwargs["env"]["BUILD_GENERATION"], str(resolutions))
                Path(command[5]).write_bytes(b"object")
                return subprocess.CompletedProcess(command, 0, "", "")

            with patch.object(build_private.subprocess, "run", side_effect=run):
                with redirect_stdout(StringIO()):
                    for generation in range(2):
                        (repo / "lakefile.toml").write_text(f'name = "project{generation}"\n')
                        build_private.build(repo, backend, include_executable=False,
                                            list_only=False, resume=False)
            self.assertEqual(resolutions, 2)
            self.assertEqual(compiles, 4)

    def test_invalid_lake_environment_fails_closed(self) -> None:
        for output in ("not json", '[]', '{"PATH": 42}'):
            with self.subTest(output=output):
                with patch.object(build_private.subprocess, "run", return_value=
                                  subprocess.CompletedProcess([], 0, output, "")):
                    with self.assertRaisesRegex(build_private.BuildError, "invalid environment"):
                        build_private.resolve_lean_environment(Path("/repository"))

    def test_topological_order_is_stable_and_dependency_first(self) -> None:
        modules = {
            "Vsa.C": build_private.Module("Vsa.C", Path("Vsa/C.lean"), ("Vsa.A",)),
            "Vsa.B": build_private.Module("Vsa.B", Path("Vsa/B.lean"), ("Vsa.A",)),
            "Vsa.A": build_private.Module("Vsa.A", Path("Vsa/A.lean"), ()),
        }
        self.assertEqual(
            [module.name for module in build_private.topological_order(modules)],
            ["Vsa.A", "Vsa.B", "Vsa.C"],
        )

    def test_topological_order_rejects_cycles(self) -> None:
        modules = {
            "Vsa.A": build_private.Module("Vsa.A", Path("Vsa/A.lean"), ("Vsa.B",)),
            "Vsa.B": build_private.Module("Vsa.B", Path("Vsa/B.lean"), ("Vsa.A",)),
        }
        with self.assertRaisesRegex(build_private.BuildError, "import cycle"):
            build_private.topological_order(modules)

    def test_output_root_must_be_outside_repository(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            base = Path(directory)
            repo = base / "repo"
            repo.mkdir()
            with self.assertRaisesRegex(build_private.BuildError, "outside repository"):
                build_private.validate_output_root(repo, repo / "private")
            outside = base / "private"
            self.assertEqual(
                build_private.validate_output_root(repo, outside), outside.resolve()
            )

    def test_dependency_change_invalidates_downstream_fingerprint(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            repo = Path(directory)
            (repo / "Vsa").mkdir()
            source_a = repo / "Vsa" / "A.lean"
            source_b = repo / "Vsa" / "B.lean"
            source_a.write_text("def a := 1\n", encoding="utf-8")
            source_b.write_text("import Vsa.A\ndef b := a\n", encoding="utf-8")
            modules = {
                "Vsa.A": build_private.Module("Vsa.A", Path("Vsa/A.lean"), ()),
                "Vsa.B": build_private.Module("Vsa.B", Path("Vsa/B.lean"), ("Vsa.A",)),
            }
            order = build_private.topological_order(modules)
            before = build_private.module_fingerprints(repo, order, "context")
            source_a.write_text("def a := 2\n", encoding="utf-8")
            after = build_private.module_fingerprints(repo, order, "context")
            self.assertNotEqual(before["Vsa.A"], after["Vsa.A"])
            self.assertNotEqual(before["Vsa.B"], after["Vsa.B"])

    def test_rejected_compiler_output_preserves_previous_object(self) -> None:
        cases = (
            (1, "error: compilation failed"),
            (0, "warning: declaration uses `sorry`"),
            (0, "warning: declaration uses 'sorry'"),
            (0, "warning: declaration uses `admit`"),
            (0, "depends on axioms: [sorryAx]"),
        )
        for returncode, diagnostic in cases:
            with (
                self.subTest(diagnostic=diagnostic),
                tempfile.TemporaryDirectory() as directory,
            ):
                root = Path(directory)
                module = build_private.Module("Vsa.A", Path("Vsa/A.lean"), ())
                target = build_private.output_path(root, module)
                target.parent.mkdir(parents=True)
                target.write_bytes(b"previous synthetic object")

                def run(command, **kwargs):
                    Path(command[7]).write_bytes(b"rejected synthetic object")
                    return subprocess.CompletedProcess(
                        command, returncode, diagnostic, ""
                    )

                with patch.object(build_private.subprocess, "run", side_effect=run):
                    with self.assertRaises(build_private.BuildError):
                        build_private.compile_module(root, root, module)
                self.assertEqual(target.read_bytes(), b"previous synthetic object")
                self.assertEqual(
                    build_private.log_path(root, module).read_text(), diagnostic
                )
                self.assertEqual(list(target.parent.iterdir()), [target])

    def test_successful_compiler_must_produce_an_object(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            module = build_private.Module("Vsa.A", Path("Vsa/A.lean"), ())
            with patch.object(
                build_private.subprocess,
                "run",
                return_value=subprocess.CompletedProcess([], 0, "", ""),
            ):
                with self.assertRaisesRegex(
                    build_private.BuildError, "produced no object"
                ):
                    build_private.compile_module(root, root, module)
            self.assertFalse(build_private.output_path(root, module).exists())

    def test_accepted_compiler_output_replaces_previous_object(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            module = build_private.Module("Vsa.A", Path("Vsa/A.lean"), ())
            target = build_private.output_path(root, module)
            target.parent.mkdir(parents=True)
            target.write_bytes(b"previous synthetic object")

            def run(command, **kwargs):
                self.assertEqual(target.read_bytes(), b"previous synthetic object")
                Path(command[7]).write_bytes(b"accepted synthetic object")
                return subprocess.CompletedProcess(
                    command, 0, "warning: unused variable", ""
                )

            with patch.object(build_private.subprocess, "run", side_effect=run):
                build_private.compile_module(root, root, module)
            self.assertEqual(target.read_bytes(), b"accepted synthetic object")
            self.assertEqual(list(target.parent.iterdir()), [target])

    def test_failed_rebuild_retains_unrelated_cache_entries(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            repo, backend = root / "repo", root / "cache"
            (repo / "Vsa").mkdir(parents=True)
            (repo / "Vsa/A.lean").write_text("def a := 1\n")
            (repo / "Vsa/B.lean").write_text("import Vsa.A\ndef b := a\n")
            (repo / "Vsa/Z.lean").write_text("def z := 3\n")
            (repo / "Vsa.lean").write_text("import Vsa.B Vsa.Z\n")
            compiled = []

            def compile_ok(repo, backend, module, **kwargs):
                compiled.append(module.name)
                target = build_private.output_path(backend, module)
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(b"synthetic object")

            def compile_fail_b(repo, backend, module, **kwargs):
                if module.name == "Vsa.B":
                    raise build_private.BuildError("synthetic rejection")
                compile_ok(repo, backend, module)

            def run(compiler):
                with patch.object(build_private, "resolve_lean_environment", return_value={}):
                    return run_resolved(compiler)

            def run_resolved(compiler):
                with patch.object(
                    build_private, "compile_module", side_effect=compiler
                ):
                    with redirect_stdout(StringIO()):
                        build_private.build(
                            repo,
                            backend,
                            include_executable=False,
                            list_only=False,
                            resume=True,
                        )

            run(compile_ok)
            before = build_private.load_manifest(backend / build_private.MANIFEST_NAME)
            (repo / "Vsa/A.lean").write_text("def a := 2\n")
            with self.assertRaisesRegex(
                build_private.BuildError, "synthetic rejection"
            ):
                run(compile_fail_b)
            failed = build_private.load_manifest(backend / build_private.MANIFEST_NAME)
            self.assertEqual(failed["Vsa.Z"], before["Vsa.Z"])
            self.assertNotEqual(failed["Vsa.A"], before["Vsa.A"])
            self.assertNotIn("Vsa.B", failed)
            compiled.clear()
            run(compile_ok)
            self.assertEqual(compiled, ["Vsa.B", "Vsa"])

    def test_interruption_after_installation_cannot_reuse_old_fingerprint(self) -> None:
        with tempfile.TemporaryDirectory() as directory:
            root = Path(directory)
            repo, backend = root / "repo", root / "cache"
            repo.mkdir()
            source = repo / "Vsa.lean"
            source.write_text("def a := 1\n")
            installed = False
            interrupt = False
            write_manifest = build_private.write_manifest

            def compile_ok(repo, backend, module, **kwargs):
                nonlocal installed
                target = build_private.output_path(backend, module)
                target.parent.mkdir(parents=True, exist_ok=True)
                target.write_bytes(source.read_bytes())
                installed = True

            def publish(path, entries):
                if interrupt and installed:
                    raise OSError(
                        "synthetic interruption before fingerprint publication"
                    )
                write_manifest(path, entries)

            def run():
                with patch.object(build_private, "resolve_lean_environment", return_value={}):
                    return run_resolved()

            def run_resolved():
                with patch.object(
                    build_private, "compile_module", side_effect=compile_ok
                ):
                    with patch.object(
                        build_private, "write_manifest", side_effect=publish
                    ):
                        with redirect_stdout(StringIO()):
                            build_private.build(
                                repo,
                                backend,
                                include_executable=False,
                                list_only=False,
                                resume=True,
                            )

            run()
            source.write_text("def a := 2\n")
            installed = False
            interrupt = True
            with self.assertRaisesRegex(OSError, "synthetic interruption"):
                run()
            self.assertNotIn(
                "Vsa",
                build_private.load_manifest(backend / build_private.MANIFEST_NAME),
            )
            source.write_text("def a := 1\n")
            installed = False
            interrupt = False
            run()
            self.assertTrue(installed)
            self.assertEqual((backend / "Vsa.olean").read_bytes(), source.read_bytes())


if __name__ == "__main__":
    unittest.main()
