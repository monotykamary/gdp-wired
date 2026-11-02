"""Build independently extractable goal archives without optional backend imports."""
import os
import pathlib
import subprocess
import tarfile


def pack_goal_files(root: pathlib.Path, goals: pathlib.Path, files: list[str]) -> str:
    if not files:
        return ""
    rel = f"research/query/.goals-{os.getpid()}.tar.zst"
    # Each job extracts only its own goal. A tar hardlink to another goal cannot be resolved then;
    # materialize every entry, including deduplicated goals in the source dump. tarfile is portable
    # here: BSD tar on the Mac has no GNU --hard-dereference flag.
    with subprocess.Popen(["zstd", "-q", "-10", "-o", str(root / rel)], stdin=subprocess.PIPE) as compressor:
        assert compressor.stdin is not None
        with compressor.stdin:
            with tarfile.open(fileobj=compressor.stdin, mode="w|", dereference=True) as archive:
                for file in files:
                    archive.add(goals.parent / file, arcname=file, recursive=False)
        code = compressor.wait()
        if code:
            raise subprocess.CalledProcessError(code, compressor.args)
    return rel
