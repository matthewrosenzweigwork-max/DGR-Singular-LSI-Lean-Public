import Tablet.Configuration
import Mathlib.Logic.Equiv.Fin.Basic
-- [TABLET NODE: ConfigurationFlatten]
def ConfigurationFlatten (d N : ℕ) :
    Configuration d N ≃ UnitAddTorus (Fin (N * d)) :=
-- BODY
  { toFun := fun X k => X (finProdFinEquiv.symm k).1 (finProdFinEquiv.symm k).2
    invFun := fun x i j => x (finProdFinEquiv (i, j))
    left_inv := by intro X; funext i j; simp
    right_inv := by
      intro x
      funext k
      change x (finProdFinEquiv (finProdFinEquiv.symm k)) = x k
      rw [Equiv.apply_symm_apply] }
