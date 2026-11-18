"""Assemble the projective Jacobian Lake package in a fresh directory."""
import argparse
from hashlib import sha256
import json
from pathlib import Path
import shutil
from tempfile import TemporaryDirectory
from urllib.request import urlopen

HERE = Path(__file__).resolve().parent
TAU_REPOSITORY = 'https://raw.githubusercontent.com/TauCetiProject/TauCeti'
TAU_REVISION = '941bb58ae04c2464c632a44d715f17b21b6bea5e'


def prepare(destination, tau_ceti=None):
    destination = destination.resolve()
    if destination.exists():
        raise ValueError('Choose a new directory for the prepared Lake project')
    destination.parent.mkdir(parents=True, exist_ok=True)
    with TemporaryDirectory(dir=destination.parent) as tmp:
        stage = Path(tmp) / 'geometry'
        stage.mkdir()
        for name, row in json.loads((HERE / 'sources.json').read_text()).items():
            target = (stage / name).resolve()
            if not target.is_relative_to(stage):
                raise ValueError('Invalid path in the source manifest')
            if row.get('dependency') == 'TauCeti':
                if tau_ceti is None:
                    with urlopen(f'{TAU_REPOSITORY}/{TAU_REVISION}/{name}', timeout=60) as response:
                        data = response.read()
                else:
                    data = (tau_ceti / name).read_bytes()
            else:
                src = (HERE.parent / row['source']).resolve()
                if not src.is_relative_to(HERE.parent):
                    raise ValueError('Invalid source in the manifest')
                data = src.read_bytes()
            if sha256(data).hexdigest() != row['sha256']:
                raise ValueError('Source differs from the verified file: ' + name)
            target.parent.mkdir(parents=True, exist_ok=True)
            target.write_bytes(data)
        for name in ('lakefile.toml', 'lake-manifest.json', 'lean-toolchain'):
            shutil.copyfile(HERE / name, stage / name)
        stage.rename(destination)


if __name__ == '__main__':
    cli = argparse.ArgumentParser(description=__doc__)
    cli.add_argument('destination', type=Path)
    cli.add_argument('--tau-ceti', type=Path, help='Read pinned Tau Ceti sources from an existing checkout')
    args = cli.parse_args()
    prepare(args.destination, args.tau_ceti)
