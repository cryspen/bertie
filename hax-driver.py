#! /usr/bin/env python3

import os
import argparse
import subprocess
import sys


def shell(command, expect=0, cwd=None, env={}):
    subprocess_stdout = subprocess.DEVNULL

    print("Env:", env)
    print("Command: ", end="")
    for i, word in enumerate(command):
        if i == 4:
            print("'{}' ".format(word), end="")
        else:
            print("{} ".format(word), end="")

    print("\nDirectory: {}".format(cwd))

    os_env = os.environ
    os_env.update(env)

    ret = subprocess.run(command, cwd=cwd, env=os_env)
    if ret.returncode != expect:
        raise Exception("Error {}. Expected {}.".format(ret, expect))


parser = argparse.ArgumentParser(description="Perform proofs using Hax.")

sub_parser = parser.add_subparsers(
    description="Extract or typecheck",
    dest="sub",
    help="Extract and typecheck F* etc. from the Bertie Rust code.",
)
extract_parser = sub_parser.add_parser("extract")

typecheck_parser = sub_parser.add_parser("typecheck")
typecheck_parser.add_argument(
    "--lax",
    action="store_true",
    dest="lax",
    help="Lax typecheck the code only",
)

options = parser.parse_args()

cargo_hax_into = ["cargo", "hax", "-C", "-p", "bertie", ";", "into"]
hax_env = {"RUSTFLAGS": "--cfg hax"}

if options.sub == "extract":
    # The extract sub command.
    shell(
        cargo_hax_into
        + [
            "-i",
            "-**::non_hax::**",
            "fstar",
        ],
        cwd=".",
        env=hax_env,
    )
elif options.sub == "typecheck":
    # Typecheck subcommand.
    custom_env = {}
    if options.lax:
        custom_env.update({"OTHERFLAGS": "--lax"})
    shell(["make", "-C", "proofs/fstar/extraction/"], custom_env)
    exit(0)
else:
    parser.print_help()
    exit(2)
