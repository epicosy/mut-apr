import re

from pathlib import Path
from typing import List, Any, Dict

from synapser.core.data.api import RepairRequest, CoverageRequest
from synapser.core.data.results import CommandData, RepairCommand
from synapser.core.database import Signal
from synapser.handlers.tool import ToolHandler
from distutils.dir_util import copy_tree


class MUTAPR(ToolHandler):
    """MUTAPR"""

    class Meta:
        label = 'mutapr'
        version = '-'

    def __init__(self, **kw):
        super().__init__(**kw)
        self.arg_matches = {'--gcc': '(\d{5}-file.c)',
                            '--bad': '(\d{5}-bad)',
                            '--good': '(\d{5}-good)'
                            }

    def repair(self, signals: dict, repair_request: RepairRequest) -> RepairCommand:
        # manifest_file = repair_request.working_dir / 'manifest.txt'
        repair_dir = Path(repair_request.working_dir, "repair")
        manifest_file = next(iter(repair_request.manifest))
        target_file = Path(manifest_file)
        repair_cwd = repair_dir / target_file.parent / target_file.stem
        repair_dir.mkdir(parents=True, exist_ok=True)
        repair_cwd.mkdir(parents=True, exist_ok=True)

        self.repair_cmd.cwd = repair_cwd
        self.repair_cmd.add_arg("", str(repair_request.build_dir / target_file))

        for opt, arg in signals.items():
            self.repair_cmd.add_arg(opt=opt, arg=f"{arg} --prefix {repair_cwd}")

        return self.repair_cmd

    def get_patches(self, working_dir: str, target_files: List[str], **kwargs) -> Dict[str, Any]:
        patches = {}
        repair_dir = Path(working_dir, "repair")

        for tf in target_files:
            patches[tf] = {}
            edits_path = repair_dir / Path(tf).parent / Path(tf).stem
            baseline_path = None
            best_path = None
            # Get original file
            for path in Path(working_dir).rglob(f'{tf}-baseline.c'):
                if path.exists():
                    baseline_path = path
                    break

            # Find fix file
            for path in Path(working_dir).rglob(f'{tf}--best.c'):
                if path.exists():
                    best_path = path
                    break

            if baseline_path is not None:
                if best_path is not None:
                    patch = self.get_patch(original=baseline_path, patch=best_path, is_fix=True)
                    patches[tf][best_path.name] = patch.change

                if edits_path.exists():
                    for file in edits_path.iterdir():
                        if not file.is_dir() and file.suffix == ".c" and file.stat().st_size > 0:
                            patch = self.get_patch(original=baseline_path, patch=file, is_fix=False)
                            patches[tf][file.stem] = patch.change

        return patches

    def _instrument(self, coverage_request: CoverageRequest) -> List[str]:
        inst_path = coverage_request.working_dir / "instrument"
        inst_path.mkdir(parents=True, exist_ok=True)
        inst_files = []

        for file in coverage_request.manifest:
            file = Path(file)
            out_path = inst_path / file.parent

            if not out_path.exists():
                out_path.mkdir()

            out_file = out_path / file.name
            args = ' '.join([f"{opt} {arg}" for opt, arg in self.configs.sections["coverage"]["args"].items()])
            program = Path(self.configs.path) / self.configs.sections["coverage"]["program"]

            with out_file.open(mode="w") as inst_file:
                cmd_data = super().__call__(
                    cmd_data=CommandData(args=f"{program} {args} {coverage_request.build_dir / file}"),
                    cmd_cwd=self.configs.path)

                if cmd_data.error:
                    self.app.log.error(cmd_data.error)
                    continue

                if cmd_data.output and cmd_data.output != '':
                    cmd_data.output = cmd_data.output.replace("fopen(\".//", 'fopen(\"/')
                    inst_file.write(cmd_data.output)
                    inst_files.append(str(out_file))

        return inst_files

    def coverage(self, signals: dict, coverage_request: CoverageRequest):
        inst_files = self._instrument(coverage_request)
        self.app.log.warning(inst_files)
        if inst_files:
            signals['--gcc'] = signals['--gcc'].replace("__INST_FILES__", ' '.join(inst_files))
            cmd_data = super().__call__(cmd_data=CommandData(args=signals['--gcc']))

            if not cmd_data.error:
                # creates folder for coverage files
                cov_dir = coverage_request.working_dir / "coverage"
                cov_dir.mkdir(parents=True, exist_ok=True)

                # insert placeholders

                signals['--good'] = signals['--good'].replace('__COV_OUT_DIR__', str(cov_dir))
                signals['--good'] = signals['--good'].replace('__RENAME_SUFFIX__', '.goodpath')

                super().__call__(cmd_data=CommandData(args=signals['--good']))

                signals['--bad'] = signals['--bad'].replace('__COV_OUT_DIR__', str(cov_dir))

                super().__call__(cmd_data=CommandData(args=signals['--bad']))

                copy_tree(str(cov_dir), str(coverage_request.build_dir))

    def parse_extra(self, extra_args: List[str], signal: Signal) -> dict:
        if signal.arg in self.arg_matches:
            args = ' '.join(extra_args)
            path = args.split()[1]
            match = re.search(self.arg_matches[signal.arg], args)

            if match:
                return {'out_file': path + "/" + match.group(0)}

        return {}


def load(nexus):
    nexus.handler.register(MUTAPR)
