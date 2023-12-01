#!/bin/bash
# Test to run Bertie against the X domains in top1m.txt

url_file="cloudflare-top100.txt"
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
        echo "    By default the util/cloudflare-top100.txt file is used with a count of 10."
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

rust_log=debug
if [ $verbose -eq 1 ]; then
    rust_log=trace
fi

while IFS= read -r line || [ -n "$line" ]; do
    if [[ $count != 'all' && $i -ge $count ]]; then
        break
    fi
    line=$(echo "${line//[$'\t\r\n']/}")

    if [[ $line = \#* ]]; then
        echo -e "Skipping ${line:1}\n"
        continue
    else
        echo "Connecting to $line"
    fi

    log=$(RUST_LOG=$rust_log \
        timeout 30s \
        cargo run -p simple_https_client -- $line 2>&1)

    if [ $verbose -eq 1 ]; then
        echo "$log"
    else
        if [[ $log == *"succeeded."* ]]; then
            echo " ... Succeeded"
        else
            echo " ... Failed"
        fi
    fi

    i=$((i + 1))
    echo ""
done <$file
