#!/usr/bin/env bash

set -e

SCRIPTPATH="$( cd -- "$(dirname "$0")" >/dev/null 2>&1 ; pwd -P )"
cd "$SCRIPTPATH"

DENYLIST=""

CP="gcp"
if ! command -v gcp &> /dev/null; then
    CP="cp"
fi

# `prepare_folder SRC DEST` copies F* files from SRC to DEST/<basename SRC>
prepare_folder() {
    original="$1"
    workdir="$2"
    find "$original" \( -name '*.fst' -o -name '*.fsti' \) -exec "$CP" --parents \{\} "$workdir" \;
}

# `patch_folder ORIGINAL DESTINATION PATCH` creates the folder
# `DESTINATION` out of the folder `ORIGINAL` given the patch `PATCH`
patch_folder() {
    original="$1"
    destination="$2"
    patch="$3"
    TEMPDIR=$(mktemp -d)
    
    prepare_folder $original "$TEMPDIR"
    
    original_basename=$(basename "$original")
    patch --directory="$TEMPDIR/$original_basename" -s -p1 < "$patch" || {
        cd "$TEMPDIR/$original_basename"
        echo '::error::Patches don'"'"'t apply. Keep in mind the CI regenerates `extraction` using the latest hax on `main`.'
        for rejection in *.rej; do
            echo "::group::cat $rejection"
            cat "$rejection"
            echo '::endgroup::'
        done
        exit 1
    }
    
    DIR="$TEMPDIR/$original_basename"
    cp -rfT "$DIR" "$destination"

    rm -rf "$TEMPDIR"
}

case $1 in
    apply)
        for target in extraction-lax extraction-panic-free; do
            find "$target" \
                 \( -name '*.fst' -o -name '*.fsti' \) \
                 -type f \
                 -exec rm -f {} +
        done

        patch_folder extraction extraction-lax \
                     extraction-lax.patch
        patch_folder extraction-lax extraction-panic-free \
                     extraction-panic-free.patch
        ;;

    create)
        TEMPDIR=$(mktemp -d)

        for i in extraction extraction-lax extraction-panic-free; do
            prepare_folder "$i" "$TEMPDIR"
        done

        (
            cd "$TEMPDIR"
            diff -ruN extraction extraction-lax > extraction-lax.patch || true
            diff -ruN extraction-lax extraction-panic-free > extraction-panic-free.patch || true

            
        )
        mv "$TEMPDIR/extraction-lax.patch" extraction-lax.patch
        mv "$TEMPDIR/extraction-panic-free.patch" extraction-panic-free.patch
        
        rm -rf "$TEMPDIR"
        ;;
    
    *)
        echo 'Usage: `'"$0"' COMMAND`'
        echo '  - `'"$0"' apply`: recreate `extraction-*` folders from the `*.patch` files'
        echo '  - `'"$0"' create`: recreate `*.patch` files from the `extraction-*` folders'
        ;;
esac
