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
extract_proverif_parser = sub_parser.add_parser("extract-proverif")
typecheck_parser = sub_parser.add_parser("typecheck")
typecheck_proverif_parser = sub_parser.add_parser("typecheck-proverif")
typecheck_parser.add_argument(
    "--lax",
    action="store_true",
    dest="lax",
    help="Lax typecheck the code only",
)
typecheck_parser.add_argument(
    "--admit",
    action="store_true",
    dest="admit",
    help="Set admit_smt_queries to true for typechecking",
)
typecheck_parser.add_argument(
    "--clean",
    action="store_true",
    dest="clean",
    help="Clean before calling make",
)

options = parser.parse_args()

cargo_hax_into = [
    "cargo",
    "hax",
    "-C",
    "-p",
    "bertie",
    "--no-default-features",
    ";",
    "into",
]
hax_env = {}

if options.sub == "extract":
    # The extract sub command.
    shell(
        cargo_hax_into
        + [
            "-i",
            "-**::non_hax::** -bertie::stream::**",
            "fstar",
        ],
        cwd=".",
        env=hax_env,
    )
elif options.sub == "extract-proverif":
    # The extract sub command.
    shell(
        cargo_hax_into
        + [
            "-i",
            " ".join([
                "-**",
                "+**::tls13handshake::put_server_hello",
                "-**::tls13utils::**",
                "-**::tls13formats::**",
                "-**::tls13crypto::**",
                      "-**::tls13cert::**"]),
            "pro-verif",
        ],
        cwd=".",
        env=hax_env,
    )
elif options.sub == "typecheck":
    # Typecheck subcommand.
    custom_env = {}
    if options.lax:
        custom_env.update({"OTHERFLAGS": "--lax"})
    if options.admit:
        custom_env.update({"OTHERFLAGS": "--admit_smt_queries true"})
    if options.clean:
        shell(["make", "-C", "proofs/fstar/extraction/", "clean"])
    shell(["make", "-C", "proofs/fstar/extraction/"], env=custom_env)
    exit(0)
elif options.sub == "typecheck-proverif":
    # Typecheck subcommand.
    custom_env = {}
    shell(["proverif", "proofs/proverif/extraction/output.pv"], env=custom_env)
    exit(0)
else:
    parser.print_help()
    exit(2)
