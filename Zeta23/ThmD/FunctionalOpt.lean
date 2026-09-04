/-
Copyright (c) 2026 Anthropic, PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
SPDX-License-Identifier: Apache-2.0
-/
/-
Public entry point for the verified variational optimization of `cFun`.

The implementation is split into definitions, bilinearity, kernel estimates,
coercivity, the Euler--Lagrange identity, and the final sharp maximum theorem.
-/
import Zeta23.ThmD.FunctionalOpt.Main
