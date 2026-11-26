/-
Copyright © 2026 François G. Dorais. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
-/
module

public import Batteries
public import BatteriesBLAS
public import BatteriesBLAS.Notation

/-!
# Batteries compatibility

As a Batteries cell, the library must be importable together with Batteries. This module imports
both, with the notation, so that a declaration or notation that clashes with one of Batteries
fails the build.
-/
