"""Portable artifact labels without resolving logical PDK symlink paths."""
import os
from pathlib import Path


def path_key(path, root):
    """Use a repository-relative label when possible, preserving symlink names."""
    path = Path(os.path.abspath(path))
    root = Path(os.path.abspath(root))
    return str(path.relative_to(root)) if path.is_relative_to(root) else str(path)


def recorded_digest(hashes, path, root):
    """Read new relative labels and historical absolute labels in this checkout."""
    wanted = path_key(path, root)
    matches = {digest for label, digest in hashes.items()
               if path_key(Path(label) if Path(label).is_absolute() else root / label, root) == wanted}
    if len(matches) > 1:
        raise RuntimeError(f"Conflicting receipt hashes for {wanted}")
    return next(iter(matches), None)
