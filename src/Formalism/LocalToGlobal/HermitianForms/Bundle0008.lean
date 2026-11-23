module

public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.InterlaceDifferenceShiftInvariant
public import Formalism.LocalToGlobal.HermitianForms.FormsTied
public import Formalism.LocalToGlobal.HermitianForms.Bundle0001
public import Formalism.LocalToGlobal.HermitianForms.Interlace
public import Formalism.SharpRestriction.GlobalSchurBounds.LinkMin
public import Formalism.LocalToGlobal.HermitianForms.TiedTwSymP
public import Formalism.LocalToGlobal.HermitianColumns.Bundle0002

@[expose] public section

-- bundled from Formalism.LocalToGlobal.HermitianForms.TiedBr
section
noncomputable section

namespace Formalism.L2.Forms

open Formalism.BasicNotions Formalism.MainNotions.product_first_zeroth_parts NumberField

variable {D : D7}

def bZ (u : D.what₂.Word) (z0 : Fin (D.R.N D.R.m) → D.host.E) :
    Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) D.host.E :=
  fun a b => if hb : (b : ℕ) < D.R.N D.R.m - 1 then iXm D a ⟨b, hb⟩ else z0 a / ((D.mem u).A.T : D.host.E)

def mZ (u : D.what₂.Word) (z0 : Fin (D.R.N D.R.m) → D.host.E) :
    D.what₂.Tau → Matrix (Fin (D.R.N D.R.m)) (Fin (D.R.N D.R.m)) ℂ :=
  atInf (embT D) (bZ u z0)⁻¹

theorem mZ_isUnit {u : D.what₂.Word} {z0 : Fin (D.R.N D.R.m) → D.host.E} (hB : IsUnit (bZ u z0).det) (τ : D.what₂.Tau) :
    IsUnit (mZ u z0 τ).det := by
  have h1 : IsUnit ((bZ u z0)⁻¹).det := Matrix.isUnit_nonsing_inv_det _ hB
  have h2 : IsUnit ((embT D τ).mapMatrix (bZ u z0)⁻¹).det := by
    rw [← RingHom.map_det]
    exact h1.map _
  exact h2

end Formalism.L2.Forms
end
end

-- bundled from Formalism.LocalToGlobal.HermitianForms.TiedTwSymAll
section
noncomputable section

open Formalism.BasicNotions NumberField IsDedekindDomain Matrix Formalism.UG

namespace Formalism.L2.Forms

attribute [local instance] Formalism.BasicNotions.Host.cmStar

structure SymmetricTwistedColumnsCompatible {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} (tp : Formalism.L2.Host.TupTied D cf nch)
    (cols : ColsTiedSym D) (Tw : TwForms D) where
  ch : Formalism.L2.Herm.TwistedCharacterData tp
  chJ : Formalism.L2.Herm.TwChJointS ch cols.herm.base
  chM : Formalism.L2.Herm.TwChMu0 ch
  forms : TwFormsTiedS D Tw ch chJ cols.forms
  lv : SymmetricTwistedLevelData forms

  same : TwLvSameS forms

  lvJ : SymmetricTwistedJointForms ch cols.forms

structure SymmetricTwistedColumnsAtPrimes {D : D7} {cf : Formalism.L2.Host.CharFrame D} {nch : NChoice D} (tp : Formalism.L2.Host.TupTied D cf nch)
    (cols : ColsTiedSym D) (Tw : TwForms D) extends SymmetricTwistedColumnsCompatible tp cols Tw where

  pt : TwPTiedS lv

  ptG : TwPAtGS pt

  ptE : TwPEvzS pt

end Formalism.L2.Forms

end
end

