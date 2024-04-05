# Extraction directories
The `extraction` directory is generated automatically by hax from the
Rust code. The `extraction-lax` and `extraction-panic-free`
are hand-edited snapshots of `extraction` at some point in time.

The edits (1) on the one hand between `extraction` and
`extraction-lax` and (2) on the other hand between
`extraction-lax` and `extraction-panic-free` are tracked
via diff files.

Whenever the rust code changes, the extracted F* code in `extraction`
changes as well. The CI then applies the diff files: if the patch
process fails or if the resulting patched F* doesn't typecheck, the CI
fails.

The bash script `./patches.sh` takes care of the diffs:
 - `./patches.sh create` creates patches out of the `extraction*` folders;
 - `./patches.sh apply` drops the `extraction-lax` and
   `extraction-panic-free` folders and re-creates them out of
   the `extraction-lax.patch` and
   `extraction-panic-free.patch` files.

# Workflow
Ideally:
 - since `extraction` is a projection from the Rust code via the hax
   toolchain, we should not commit it in the repository;
 - since `extraction-lax` and `extraction-panic-free` are
   created via the diff files, we should not commit them either in the
   repository.

Currently, we do check those 3 folders in. Thus, when we change
anything in the F* proofs, we should always make sure we keep the diff
files and those folder in a coherent state.

In other words, this means that the last commit of each PR should be
about regeneration of diff files (using the command `./patches.sh
create`) and regeneration of the `extraction` folder.
