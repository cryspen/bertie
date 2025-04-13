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
extract_parser = sub_parser.add_parser("extract-fstar")
extract_parser = sub_parser.add_parser("extract-ssprove")
extract_parser = sub_parser.add_parser("extract-coq")
extract_proverif_parser = sub_parser.add_parser("extract-proverif")
typecheck_parser = sub_parser.add_parser("typecheck")
patch_proverif_parser = sub_parser.add_parser("patch-proverif")
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
    "-p",
    "rand_core",
    "--no-default-features",
    "-F std",
    ";",
    "into",
]

cargo_hax_into_ssp = [
    "cargo",
    "hax",
    "-C",
    "-p",
    "bertie",
    "--no-default-features",
    "--features",
    "std",
    ";",
    "into",
]

cargo_hax_into_pv = [
    "cargo",
    "hax",
    "-C",
    "-p",
    "bertie",
    "--no-default-features",
    "--features",
    "hax-pv,std",
    ";",
    "into",
]
hax_env = {}

if options.sub == "extract-fstar":
    # The extract sub command.
    shell(
        cargo_hax_into
        + [
            "-i",
            "-**::non_hax::** -bertie::stream::**",
            "fstar",
            "--interfaces",
            "+** +!bertie::tls13crypto::** +!bertie::tls13utils::** +!bertie::tls13cert::**"
        ],
        cwd=".",
        env=hax_env,
    )
elif options.sub == "extract-ssprove":
    # The extract sub command.
    shell(
        cargo_hax_into_ssp
        + [
            "-i",
            " ".join([
                "-**",
                "+~**::tls13keyscheduler::**",
                "+~**::tls13utils::parse_failed", # transitive dependencies required
                "+~**::tls13crypto::zero_key", # transitive dependencies required
                ]),
            "ssprove",
        ],
        cwd=".",
        env=hax_env,
    )
elif options.sub == "extract-coq":
    # The extract sub command.
    shell(
        cargo_hax_into_ssp
        + [
            "-i",
            " ".join([
                "-**",
                "+~**::tls13handshake::**",
                "+~**::server::lookup_db", # to include transitive dependency on tls13utils
                "+~**::tls13keyscheduler::**",
                "+~**::tls13utils::parse_failed", # transitive dependencies required
                "+~**::tls13crypto::zero_key", # transitive dependencies required
                ]),
            "coq",
        ],
        cwd=".",
        env=hax_env,
    )
elif options.sub == "extract-handshake":
    # The extract sub command.
    shell(
        cargo_hax_into
        + [
            "-i",
            "-** +~bertie::tls13handshake::**",
            "fstar",
            "--interfaces",
            "+!** +bertie::tls13handshake::**",
        ],
        cwd=".",
        env=hax_env,
    )
elif options.sub == "extract-proverif":
    # The extract sub command.
    shell(
        cargo_hax_into_pv
        + [
            "-i",
            " ".join(
                [
                    "-**",
                    "+~**::tls13handshake::**",
                    "+~**::server::lookup_db",  # to include transitive dependency on tls13utils
                    "+~**::tls13utils::parse_failed",  # transitive dependencies required
                    "+!**::tls13utils::concat_inner",
                    "+!**::tls13utils::eq_inner",
                    "+!**::tls13utils::check_eq_inner",
                    "+!**::tls13formats::handshake_data::to_bytes_inner",
                    "+!**::tls13formats::handshake_data::to_two_inner",
                    "+!**::tls13formats::handshake_data::to_four_inner",
                    "+!**::tls13crypto::hash",
                    
                ]
            ),
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
elif options.sub == "patch-proverif":
    custom_env = {}
    shell(
        [
            "patch",
            "proofs/proverif/extraction/lib.pvl",
            "proofs/proverif/patches/lib.patch",
        ],
        env=custom_env,
    )
    shell(
        [
            "patch",
            "proofs/proverif/extraction/analysis.pv",
            "proofs/proverif/patches/analysis.patch",
        ],
        env=custom_env,
    )
    exit(0)
elif options.sub == "typecheck-proverif":
    # Typecheck subcommand.
    custom_env = {}
    shell(
        [
            "proverif",
            "-lib",
            "proofs/proverif/handwritten_lib",
            "-lib",
            "proofs/proverif/extraction/lib",
            "proofs/proverif/extraction/analysis.pv",
        ],
        env=custom_env,
    )
    exit(0)
else:
    parser.print_help()
    exit(2)
