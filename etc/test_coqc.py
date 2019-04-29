#!/usr/bin/env python3

import os.path
from os.path import join
from datetime import datetime, timedelta

from coqc import CoqcFilter, Classify


class MemDb:
    def __init__(self):
        self.qeds = {}
        self.files = {}

    def add_qed(self, fname, ident, time):
        self.qeds[(fname, ident)] = time

    def add_file(self, fname, time):
        self.files[fname] = time

    def close(self):
        pass


def test_classify_qed():
    assert Classify.is_qed("Qed.")
    assert Classify.is_qed("Time Qed.")
    assert Classify.is_qed("Time  Qed.")

    assert not Classify.is_qed("Qed")
    assert not Classify.is_qed("NotQed.")


def test_classify_def():
    assert (
        Classify.get_def(
            r"""Definition σ :
    forall (x:nat), x + 1000 = x + 1000 :=
    fun x => eq_refl (x + (500+500))."""
        )
        == "σ"
    )

    assert Classify.get_def(r"""Require Import Utf8.""") is None


def test_classify_time():
    assert Classify.get_time(
        r"""Chars 110 - 119 [Print~σ.] 0.009 secs (0.006u,0.003s)"""
    ) == (110, 119, 0.009)

    assert Classify.get_time(
        r"""Chars 120 - 139 [Theorem~thm~:~True.] 0. secs (0.u,0.s)"""
    ) == (120, 139, 0.0)

    assert Classify.get_time(r"""Debug: (* debug auto: *)""") is None

    assert (
        Classify.get_time(
            r"""σ = λ x : nat, eq_refl
     : ∀ x : nat, x + 1000 = x + 1000"""
        )
        is None
    )


FIXTURE_DIR = join(os.path.dirname(os.path.realpath(__file__)), "test_coqc")


def test_filter():
    db = MemDb()
    start = datetime.now()
    vfile = join(FIXTURE_DIR, "test.v")
    filter = CoqcFilter(vfile, db, None, start)
    with open(join(FIXTURE_DIR, "test.v.out"), "rb") as f:
        for line in f:
            filter.line(line)
    assert (
        filter.chars(21, 111)
        == r"""Definition σ : forall (x:nat), x + 1000 = x + 1000 :=
  fun x => eq_refl (x + (500+500))."""
    )
    end_t = start + timedelta(seconds=0.5)
    filter.done(end_t=end_t)

    assert db.qeds == {
        (vfile, "thm"): 0.0,
        (vfile, "helpful"): 0.037,
        (vfile, "thm'"): 0.0,
    }
    assert db.files[vfile] == 0.5

    for fname, qeds in {"Abstract.v": {"abstract_away_helper": 0.0}}.items():
        vfile = join(FIXTURE_DIR, fname)
        db = MemDb()
        filter = CoqcFilter(vfile, db, None, datetime.now())
        with open(vfile + ".out", "rb") as f:
            for line in f:
                filter.line(line)
        filter.done()
        expected_qeds = dict(((vfile, ident), t) for ident, t in qeds.items())
        assert db.qeds == expected_qeds
