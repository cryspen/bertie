#!/bin/bash
# Test to run Bertie against the X domains in top1m.txt

url_file="top1m.txt"
count=10
verbose=0
while [ $# -gt 0 ]; do
    case "$1" in
    --url-file)
        url_file=$2
        shift
        ;;
    --count)
        count=$2
        shift
        ;;
    -e)
        set -e
        ;;
    -v)
        set -x
        verbose=1
        ;;
    *)
        echo "Usage:"
        echo "    $0 --url-file <url-file> --count <#-of-urls-to-test> [-e-v]"
        echo "    -e aborts the script on an error"
        echo "    -v makes the script more verbose"
        echo ""
        echo "    By default the util/top1m.txt file is used with a count of 10."
        exit 2
        ;;
    esac
    shift
done

cwd=$(
    cd $(dirname $0)
    pwd -P
)

cd $cwd/../

file="util/$url_file"
i=0

rust_log=
if [ $verbose -eq 1 ]; then
    rust_log=debug
fi

while IFS= read -r line || [ -n "$line" ]; do
    if [ $i -ge $count ]; then
        break
    fi
    line=$(echo "${line//[$'\t\r\n']/}")
    echo "Connecting to $line"

    log=$(RUST_LOG=$rust_log \
        timeout 30s \
        cargo run -p simple_https_client \
        --no-default-features --features evercrypt -- \
        $line 2>&1)

    if [ $verbose -eq 1 ]; then
        echo "$log"
    else
        echo "$log" | grep 'Error:\|succeeded'
    fi

    i=$((i + 1))
    echo -e " ---------------------"
done <$file
