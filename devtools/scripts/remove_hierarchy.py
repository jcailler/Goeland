import os
import shutil
import argparse


def flatten_folder(
    root: str,
    output_dir: str | None = None,
    dry_run: bool = False,
    on_conflict: str = "rename",
) -> None:
    """
    Copy/move all files nested inside *root* into *output_dir*, then remove
    empty subdirs from *root* (only when no separate output_dir is given).

    Args:
        root:        Path to the source folder to flatten.
        output_dir:  Destination folder for all collected files.
                     Defaults to *root* itself (in-place flattening).
        dry_run:     If True, only print what would happen without touching files.
        on_conflict: What to do when a filename already exists in the output dir.
                     "rename"    – append _1, _2, … until the name is free (default)
                     "overwrite" – replace the existing file
                     "skip"      – leave the nested file in place
    """
    root = os.path.abspath(root)
    if not os.path.isdir(root):
        raise ValueError(f"Not a directory: {root}")

    separate_output = output_dir is not None
    out = os.path.abspath(output_dir) if separate_output else root

    if not dry_run:
        os.makedirs(out, exist_ok=True)

    # Collect every file that is NOT already directly in the output dir
    to_move: list[tuple[str, str]] = []  # (src_path, dest_path)

    for dirpath, dirnames, filenames in os.walk(root):
        # When flattening in-place, skip files already at root level
        if not separate_output and os.path.abspath(dirpath) == root:
            continue
        # When using a separate output dir, skip files that are inside it
        if separate_output and os.path.abspath(dirpath).startswith(out):
            continue
        for filename in filenames:
            src = os.path.join(dirpath, filename)
            dest = _resolve_dest(out, filename, on_conflict)
            to_move.append((src, dest))

    if not to_move:
        print("Nothing to do – all files are already at the destination.")
        return

    # Copy to separate output dir, or move in-place
    action = shutil.copy2 if separate_output else shutil.move
    action_label = "Copying" if separate_output else "Moving"

    for src, dest in to_move:
        if on_conflict == "skip" and os.path.exists(dest):
            print(f"[skip] {src}")
            continue
        if dry_run:
            print(f"[dry-run] {src}  →  {dest}")
        else:
            print(f"{action_label}: {src}  →  {dest}")
            action(src, dest)

    if dry_run or separate_output:
        return

    # Remove directories that are now empty (deepest first, in-place mode only)
    for dirpath, dirnames, filenames in os.walk(root, topdown=False):
        if os.path.abspath(dirpath) == root:
            continue
        try:
            os.rmdir(dirpath)           # only succeeds if the dir is empty
            print(f"Removed empty dir: {dirpath}")
        except OSError:
            print(f"Kept non-empty dir: {dirpath}")


def _resolve_dest(root: str, filename: str, on_conflict: str) -> str:
    dest = os.path.join(root, filename)
    if not os.path.exists(dest) or on_conflict == "overwrite":
        return dest
    if on_conflict == "skip":
        return dest  # caller checks this to decide whether to skip
    # "rename" mode – append _1, _2, …
    name, ext = os.path.splitext(filename)
    counter = 1
    while True:
        new_name = f"{name}_{counter}{ext}"
        dest = os.path.join(root, new_name)
        if not os.path.exists(dest):
            return dest
        counter += 1


if __name__ == "__main__":
    parser = argparse.ArgumentParser(
        description="Flatten a folder: move every nested file up to the root level."
    )
    parser.add_argument("folder", help="Path to the root folder to flatten")
    parser.add_argument(
        "--output-dir", "-o",
        default=None,
        metavar="DIR",
        help=(
            "Destination folder for the flattened files. "
            "If omitted, files are moved in-place inside the source folder. "
            "If provided, files are copied to DIR and the source is left untouched."
        ),
    )
    parser.add_argument(
        "--dry-run",
        action="store_true",
        help="Preview changes without moving anything",
    )
    parser.add_argument(
        "--on-conflict",
        choices=["rename", "overwrite", "skip"],
        default="rename",
        help="What to do when two files share the same name (default: rename)",
    )
    args = parser.parse_args()

    flatten_folder(
        args.folder,
        output_dir=args.output_dir,
        dry_run=args.dry_run,
        on_conflict=args.on_conflict,
    )