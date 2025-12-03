/-
Copyright (c) 2025 Lean FRO LLC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: David Thrane Christiansen
-/

import VersoBlog
open Verso Genre Blog

open Code.External

set_option verso.exampleProject "../lean_content"

#doc (Page) "Set up" =>
%%%
%%%

```anchor Matrix.SpecialLinearGroup.rel (module := SumOfThreeSq.Mathlib.SpecialLinearGroup.Basic)
def rel : Setoid (Matrix n n R) := MulAction.orbitRel (SpecialLinearGroup n R) (Matrix n n R)
```
