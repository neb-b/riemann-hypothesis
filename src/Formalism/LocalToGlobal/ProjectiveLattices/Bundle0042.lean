module

public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0039
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.Bundle0038
public import Formalism.LocalToGlobal.ProjectiveLattices.CompHt
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.Bundle0006
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0038

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.TieReadSS
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

theorem holSub_comp_SS {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type}
    (X : Comp → Data E r) (la : ∀ c, Wt (X c).Ψ r) (P : FDSec X) (hP : P ∈ holSub X la) (k : Comp) :
    P k ∈ (X k).SS (la k) := by
  have hM := siegelSpaceAlgebra_holds (E := E)
  induction hP using Submodule.span_induction with
  | mem x hx => exact hx k
  | zero => exact (hM r (X k) (la k) (la k) 0).1.1
  | add x y _ _ hx hy => exact (hM r (X k) (la k) (la k) 0).1.2.1 _ hx _ hy
  | smul a x _ hx => exact (hM r (X k) (la k) (la k) 0).1.2.2 a _ hx

variable {D : D7} {T : Top D} (h : LawsP T) (j : ℕ) (hj : InR D j)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.TieUpC
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.Gaps.EtaleWeightGaps ReciprocityTheory.ChartRestriction.G.Geo.Tor
  ReciprocityTheory.ChartRestriction.G.FD TensorProduct

variable {D : D7} {T : Top D}


set_option maxHeartbeats 1000000 in
abbrev OmSK (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)
    {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (Z : Comp (T.Q.Xo j) T.Q.c) : Type :=
  RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w ⧸
    Ideal.map (phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w) (Jid (recPlus h j hj) la G.w)


set_option maxHeartbeats 4000000 in
def qZ (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)
    {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (Z : Comp (T.Q.Xo j) T.Q.c)
    (F : (recB h.toLawsCore).Cusp j wF) : OmSK h j hj hG hT G la Z :=
  Ideal.Quotient.mk (Ideal.map (phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w)
      (Jid (recPlus h j hj) la G.w))
    (lwZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w
      (algebraMap (Rp (recPlus h j hj) la G.N) (Lw (recPlus h j hj) la G.w)
        (emb (recPlus h j hj) la G.N ((recPlus h j hj).inc wF F))))


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
def algZ (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (hT : GenFromTest (T.Q.Xo j) T.Q.c hG)
    {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (Z : Comp (T.Q.Xo j) T.Q.c) :
    Kp (recPlus h j hj) la G.N →+* OmSK h j hj hG hT G la Z :=
  (Ideal.Quotient.mk (Ideal.map (phiZ (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w)
      (Jid (recPlus h j hj) la G.w))).comp
    (algebraMap (Kp (recPlus h j hj) la G.N) (RZs (recPlus h j hj) la G.N (Om Z) (formsEvR j hG hT Z) G.w))


set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 1000000 in
def TieSSt (h : LawsP T) (j : ℕ) (hj : InR D j) (hG : GenFrEx (T.Q.Xo j) T.Q.c)
    (hT : GenFromTest (T.Q.Xo j) T.Q.c hG) {ka wL wF : WeightFamilies.Wt D j} (G : GlobalFamilyData (recPlus h j hj) ka wL wF)
    (la : HeightOneSpectrum (𝓞 (recB h.toLawsCore).KO)) (g0 : (recB h.toLawsCore).Cusp j wF) : Prop :=
  letI : ∀ Z, Module (Kp (recPlus h j hj) la G.N) (OmSK h j hj hG hT G la Z) := fun Z =>
    (algZ h j hj hG hT G la Z).toModule
  (∃ e : SectionSheafQuotient (recPlus h j hj) la G.w wF ≃ₗ[Kp (recPlus h j hj) la G.N] (∀ Z, OmSK h j hj hG hT G la Z),
    ∀ (F : (recB h.toLawsCore).Cusp j wF) (Z : Comp (T.Q.Xo j) T.Q.c),
      e (resF G la F) Z * qZ h j hj hG hT G la Z g0 = qZ h j hj hG hT G la Z F) ∧
  G.del = ∑ᶠ Z : Comp (T.Q.Xo j) T.Q.c, Module.finrank (Kp (recPlus h j hj) la G.N) (OmSK h j hj hG hT G la Z)





end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.TieUpR
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD

variable {D : D7} {T : Top D}

def KappaTie (j : ℕ) (hG : GenFrEx (T.Q.Xo j) T.Q.c) (κ : Comp (T.Q.Xo j) T.Q.c → (T.U j T.σ₀).Comp) : Prop :=
  ∀ (Z : Comp (T.Q.Xo j) T.Q.c) (u : WeightFamilies.Wt D j) (f : T.R j), f ∈ sec (T.Q.Xo j) T.Q.c (wtA u) u.n →
    (evC hG Z f = 0 ↔ ∀ x ∈ ((T.U j T.σ₀).X (κ Z)).dom, rdU (T.U j T.σ₀) f (κ Z) x = 0)

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.UnifGam
section
noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped Matrix

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Lat

variable {E : Type} [Field E] [NumberField E] {r : ℕ}

theorem smul_coord (x : 𝓞 E) (w : Fin r → E) (a : Fin r) : (x • w) a = (x : E) * w a := by
  simp [Algebra.smul_def]

end Lat

section Herm

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}

theorem herm_smul_left (G : Matrix (Fin r) (Fin r) E) (c : 𝓞 E) (u w : Fin r → E) :
    herm G (c • u) w = (c : E) * herm G u w := by
  simp only [herm, smul_coord, Finset.mul_sum, mul_assoc]

theorem herm_smul_right (G : Matrix (Fin r) (Fin r) E) (c : 𝓞 E) (u w : Fin r → E) :
    herm G u (c • w) = cc (c : E) * herm G u w := by
  simp only [herm, smul_coord, Finset.mul_sum, cc, map_mul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => by ring

end Herm

section Gam

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {r : ℕ}

end Gam

end Formalism.L2.Pj
end
end

