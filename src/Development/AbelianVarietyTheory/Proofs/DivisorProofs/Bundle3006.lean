module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0541
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2866
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0012
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ToroidalCompactificationBis
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0019
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.NormNegCmConstantEqAtAllEmbeddings
public import Formalism.LocalRingCardinality.Bundle0003
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0059
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0053
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0041
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0043
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0891
public import Development.AbelianVarietyTheory.Definitions.Divisors.IsHeightIffOfDegreeEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.WedgeNrmLeOfWedgeNormLe
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0048
public import Development.AbelianVarietyTheory.Definitions.Divisors.MemLevEigenIffTransl
public import Formalism.LocalToGlobal.IndefiniteForms.IndefiniteTree.RealCubicMeans.LogMeanShares.LogMeanStatements.HSClaim
public import Development.AbelianVarietyTheory.Definitions.Divisors.GenRatios
public import Development.AbelianVarietyTheory.Definitions.Divisors.BadElt
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KeepsCuspLatticeNorm
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2997
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0071
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0055
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2313
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2797
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2228
public import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsIsDeepOfField
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2976
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2970
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsDominantToUnitLeft
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2175
public import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2953
public import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsDatNeZero
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0064
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0362
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0006
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbelianHodgeDeRham
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2974
public import Development.AbelianVarietyTheory.Definitions.Divisors.AxesVanishingStructureSheafDegOne
public import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.IsScalarTowerOfAlgebraMapEq
public import Development.AbelianVarietyTheory.Definitions.Divisors.HasRigidCoords
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0017
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2728
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2178
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2760
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2769
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2750
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2828
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2994
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2922
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2742
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2978
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle2977
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0068

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoveringRepresentationTypeFrame
section
open CategoryTheory AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Theta
open GlobalTheory GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop GlobalTheory.HSApp GlobalTheory.DegVal GlobalTheory.DegCmp
open GlobalTheory.AllWt (Psi wtOf cuspOn cuspW latOn latW normOn petOn GoodOn GoodW rankOn degOn rankW)
open GlobalTheory.CompHt (hodgeWt)
open GlobalTheory.LevDesc (TypeFrame grpHR grpGHR latN levDet secRing transl pull KeepsCusp)
open GlobalTheory.IndefiniteRowSideFullHecke.LevelStructureAutomorphisms (LevelAut)
open GlobalTheory.BadCount
open scoped TensorProduct

set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.BadEmb

section Abstract

variable {K Γ A : Type} [Field K] [Group Γ] [CommRing A] [Algebra K A] (B : Subalgebra K A) (tr : Γ → A →ₐ[K] A)
  (t1 : ∀ f, tr 1 f = f) (tm : ∀ g h f, tr (g * h) f = tr g (tr h f)) (tB : ∀ g, ∀ f ∈ B, tr g f ∈ B)

def subAct : Γ →* (B →ₐ[K] B) where
  toFun g := ((tr g).comp B.val).codRestrict B fun f => tB g f f.2
  map_one' := AlgHom.ext fun f => Subtype.ext (t1 f)
  map_mul' g h := AlgHom.ext fun f => Subtype.ext (tm g h f)

theorem det_mem_nonZeroDivisors (S : Subgroup Γ) [Fintype S] [DecidableEq S] (u : B)
    (h : ∀ f ∈ B, (Matrix.of fun a b : S => tr ((a * b : S) : Γ)⁻¹ u).det * f = 0 → f = 0) :
    (Matrix.of fun a b : S => subAct B tr t1 tm tB ((a : Γ) * b) u).det ∈ nonZeroDivisors B := by
  have e : B.val.toRingHom.mapMatrix (Matrix.of fun a b : S => subAct B tr t1 tm tB ((a : Γ) * b) u) =
      ((Matrix.of fun a b : S => tr ((a * b : S) : Γ)⁻¹ u).submatrix (Equiv.inv S) (Equiv.inv S)).transpose := by
    refine Matrix.ext fun a b => ?_
    show tr ((a : Γ) * b) u = tr ((b⁻¹ * a⁻¹ : S) : Γ)⁻¹ u
    simp
  rw [mem_nonZeroDivisors_iff_left]
  intro f hf
  refine Subtype.ext (h f f.2 ?_)
  have h1 := congrArg B.val.toRingHom hf
  rw [map_mul, map_zero, RingHom.map_det, e, Matrix.det_transpose, Matrix.det_submatrix_equiv_self] at h1
  exact h1

def subEquiv (V : Submodule K A) (hV : ∀ f ∈ V, f ∈ B) : V.comap B.val.toLinearMap ≃ₗ[K] V where
  toFun f := ⟨f.1.1, f.2⟩
  invFun f := ⟨⟨f.1, hV _ f.2⟩, f.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

def subRep (V : Submodule K A) (hV : ∀ g, ∀ f ∈ V, tr g f ∈ V) : Representation K Γ (V.comap B.val.toLinearMap) where
  toFun g := (subAct B tr t1 tm tB g).toLinearMap.restrict fun f hf => hV g f hf
  map_one' := LinearMap.ext fun f => Subtype.ext (Subtype.ext (t1 f))
  map_mul' g h := LinearMap.ext fun f => Subtype.ext (Subtype.ext (tm g h f))


include t1 tm tB in
theorem embReg_of_submodules [Algebra K ℂ] [Finite Γ] (Vm V V₁ V₂ U : Submodule K A) (bm : ∀ f ∈ Vm, f ∈ B)
    (b0 : ∀ f ∈ V, f ∈ B) (b2 : ∀ f ∈ V₂, f ∈ B) (bU : ∀ f ∈ U, f ∈ B)
    (m0 : ∀ f ∈ Vm, ∀ u ∈ U, f * u ∈ V) (m1 : ∀ f ∈ V, ∀ u ∈ U, f * u ∈ V₁) (m2 : ∀ f ∈ V₁, ∀ u ∈ U, f * u ∈ V₂)
    (kU : ∀ g, ∀ f ∈ U, tr g f ∈ U) (k0 : ∀ g, ∀ f ∈ V, tr g f ∈ V) (k1 : ∀ g, ∀ f ∈ V₁, tr g f ∈ V₁)
    (f0 : FiniteDimensional K V) (f2 : FiniteDimensional K V₂) (t : ℝ) (ht : 0 ≤ t)
    (hr : (Module.finrank K V₂ : ℝ) ≤ t * Module.finrank K Vm)
    (S₀ S : Subgroup Γ) (i0 : Fintype S₀) (d0 : DecidableEq S₀) (i1 : Fintype S) (d1 : DecidableEq S)
    (h0 : ∃ u ∈ U, ∀ f ∈ B, (Matrix.of fun a b : S₀ => tr ((a * b : S₀) : Γ)⁻¹ u).det * f = 0 → f = 0)
    (h1 : ∃ u ∈ U, ∀ f ∈ B, (Matrix.of fun a b : S => tr ((a * b : S) : Γ)⁻¹ u).det * f = 0 → f = 0)
    (ρ : Representation ℂ Γ (ℂ ⊗[K] V)) (χ : Γ →* ℂˣ) (lam : S₀ →* ℂˣ)
    (hρ : ∀ (g : Γ) (v w : V), (w : A) = tr g v → ρ g ((1 : ℂ) ⊗ₜ[K] v) = ((χ g : ℂˣ) : ℂ) • ((1 : ℂ) ⊗ₜ[K] w)) :
    ∃ n : ℕ, EmbReg ρ S n ∧ (n : ℝ) * Nat.card S ≤ t * Nat.card S₀ * Module.finrank ℂ (eig ρ S₀ lam) := by
  obtain ⟨u0, hu0, r0⟩ := h0
  obtain ⟨u, hu, r1⟩ := h1
  haveI := (subEquiv B V b0).symm.finiteDimensional
  haveI := (subEquiv B V₂ b2).symm.finiteDimensional
  refine GlobalTheory.BadCount.embReg_count_of_ranks K Γ B (ℂ ⊗[K] V) (subAct B tr t1 tm tB) S₀ S ⟨u0, bU _ hu0⟩ ⟨u, bU _ hu⟩
    (det_mem_nonZeroDivisors B tr t1 tm tB S₀ _ r0) (det_mem_nonZeroDivisors B tr t1 tm tB S _ r1)
    (Vm.comap B.val.toLinearMap) (V.comap B.val.toLinearMap) (V₁.comap B.val.toLinearMap) (V₂.comap B.val.toLinearMap)
    (subRep B tr t1 tm tB V k0) (fun _ _ => rfl)
    (fun h x hx => m0 _ hx _ (kU _ _ hu0)) (fun h x hx => m1 _ hx _ (kU _ _ hu)) (fun h x hx => k1 _ _ hx)
    (fun h x hx => m2 _ hx _ (kU _ _ hu)) t ht ?_
    (TensorProduct.mk K ℂ _ 1 ∘ₗ (subEquiv B V b0).toLinearMap) ?_ ρ χ (fun g v => hρ g _ _ rfl) lam
  · rwa [(subEquiv B V₂ b2).finrank_eq, (subEquiv B Vm bm).finrank_eq]
  · exact IsBaseChange.of_equiv ((subEquiv B V b0).baseChange K ℂ _ _) fun x => by simp

end Abstract

section General

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} (hpq : 1 ≤ Dw.p + Dw.q) (hA : l.A.Coprime l.M)
  {r : ℕ} (U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r)

theorem transl_mem {G : WTZ E} (k : KeepsCusp U G) (g : LevelAut Dw l) (f : Rul Xo c) (hf : f ∈ cuspW Xo c U G) :
    transl Xo c g f ∈ cuspW Xo c U G := by
  rw [← LevDesc.pull_inv]; exact k _ f hf

theorem cusp_mem_secRing (G : WTZ E) (f : Rul Xo c) (hf : f ∈ cuspW Xo c U G) : f ∈ secRing Xo c :=
  LevDesc.mem_secRing (AllWt.cuspW_le_secZ _ hf)


include hpq hA in
theorem embReg_of_cusp (Gm G G₁ G₂ W : WTZ E) (em : Even Gm.2) (eW : Even W.2) (a0 : Gm + W = G) (a1 : G + W = G₁)
    (a2 : G₁ + W = G₂) (kW : KeepsCusp U W) (k0 : KeepsCusp U G) (k1 : KeepsCusp U G₁)
    (f0 : FiniteDimensional c.F (cuspW Xo c U G)) (f2 : FiniteDimensional c.F (cuspW Xo c U G₂)) (t : ℝ) (ht : 0 ≤ t)
    (hr : (Module.finrank c.F (cuspW Xo c U G₂) : ℝ) ≤ t * Module.finrank c.F (cuspW Xo c U Gm))
    (S₀ S : Subgroup (LevelAut Dw l))
    (h0 : ∃ u ∈ cuspW Xo c U W, ∀ f ∈ secRing Xo c, levDet Xo c S₀ u * f = 0 → f = 0)
    (h1 : ∃ u ∈ cuspW Xo c U W, ∀ f ∈ secRing Xo c, levDet Xo c S u * f = 0 → f = 0)
    (ρ : Representation ℂ (LevelAut Dw l) (ℂ ⊗[c.F] cuspW Xo c U G)) (χ : LevelAut Dw l →* ℂˣ) (lam : S₀ →* ℂˣ)
    (hρ : ∀ (g : LevelAut Dw l) (v w : cuspW Xo c U G), (w : Rul Xo c) = transl Xo c g v →
      ρ g ((1 : ℂ) ⊗ₜ[c.F] v) = ((χ g : ℂˣ) : ℂ) • ((1 : ℂ) ⊗ₜ[c.F] w)) :
    ∃ n : ℕ, EmbReg ρ S n ∧ (n : ℝ) * Nat.card S ≤ t * Nat.card S₀ * Module.finrank ℂ (eig ρ S₀ lam) := by
  have e0 : Even G.2 := a0 ▸ em.add eW
  have e1 : Even G₁.2 := a1 ▸ e0.add eW
  exact embReg_of_submodules (secRing Xo c) (transl Xo c) (LevDesc.transl_one hpq hA) (LevDesc.transl_mul hpq hA)
    (fun g f hf => by rw [← LevDesc.pull_inv]; exact LevDesc.pull_mem_secRing hpq hA _ hf)
    (cuspW Xo c U Gm) (cuspW Xo c U G) (cuspW Xo c U G₁) (cuspW Xo c U G₂) (cuspW Xo c U W)
    (cusp_mem_secRing U _) (cusp_mem_secRing U _) (cusp_mem_secRing U _) (cusp_mem_secRing U _)
    (fun f hf u hu => a0 ▸ SlopeRec.mul_mem_cuspW em eW hf hu) (fun f hf u hu => a1 ▸ SlopeRec.mul_mem_cuspW e0 eW hf hu)
    (fun f hf u hu => a2 ▸ SlopeRec.mul_mem_cuspW e1 eW hf hu) (transl_mem U kW) (transl_mem U k0) (transl_mem U k1)
    f0 f2 t ht hr S₀ S _ _ _ _ h0 h1 ρ χ lam hρ

end General

section Weights

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} (Dw : Datum H)

theorem shiftG_add (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) (s t : ℤ) :
    shiftG Dw a n s + wtOf Dw (t • hodgeWt Dw) 0 = shiftG Dw a n (s + t) := by
  rw [shiftG, shiftG, add_smul, add_assoc]
  exact congrArg _ (AllWt.wtOf_add _ _ 0 0).symm

theorem shiftG_zero' (a : (E →+* ℂ) × ℕ → ℕ) (n : ℕ) : shiftG Dw a n 0 = wtZ a n := by
  rw [shiftG, zero_smul, AllWt.wtOf_zero, add_zero]

theorem even_shiftG (a : (E →+* ℂ) × ℕ → ℕ) {n : ℕ} (hn : Even n) (s : ℤ) : Even (shiftG Dw a n s).2 :=
  Even.add ((Int.even_coe_nat n).2 hn) (AllWt.even_wtOf _ _)

theorem antitone_add_hodge (v : AllWt.Weight Dw) (τ : Psi H) (hv : Antitone (v τ)) {t : ℤ} (ht : 0 ≤ t) :
    Antitone ((v + t • hodgeWt Dw) τ) := by
  intro a b hab
  have h := hv hab
  have hab' : (a : ℕ) ≤ b := hab
  simp only [hodgeWt, CompHt.barWt, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  split_ifs <;> omega

theorem gap_add_hodge (hp : 1 ≤ Dw.p) (hq : 1 ≤ Dw.q) (v : AllWt.Weight Dw) (τ : Psi H) (t : ℤ) :
    gap ((v + t • hodgeWt Dw) τ) (Dw.p - 1) = gap (v τ) (Dw.p - 1) + t := by
  have hk : Dw.p - 1 + 1 < Dw.p + Dw.q := by omega
  simp only [gap, dif_pos hk, Pi.add_apply, Pi.smul_apply, hodgeWt, CompHt.barWt, Fin.val_mk, smul_eq_mul]
  split_ifs <;> first | omega | ring

end Weights

theorem finrank_of_goodAt {D : D7} {T : Core D} {j : ℕ} {Y : Deep T j} {G : WTZ D.host.E} (h : Y.GoodAt G) :
    FiniteDimensional Y.d.c₂.F (Y.V G) ∧ Module.finrank Y.d.c₂.F (Y.V G) = Y.rk G := by
  refine ⟨Module.Finite.of_basis h.1.some.2.1.1, ?_⟩
  show _ = Module.finrank Y.d.c₂.F (Submodule.span Y.d.c₂.F (latW Y.U G : Set (Y.V G)))
  rw [h.2.2, finrank_top]

theorem embReg_deep {D : D7} {T : CoreJ D} (hL : LawsJ T) {j : ℕ} (hp1 : 1 ≤ (T.Q.Dw j).p) (hq1 : 1 ≤ (T.Q.Dw j).q)
    (hf : 2 < Module.finrank ℚ D.host.E / 2) (hj : InR D j) (Y : Deep T.toCore j) {e : ℕ} {o : ℝ} (hY : Y.Good e o)
    (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) (hn : Even n) (c : ℤ) (g0 : Y.GoodAt (wtZ a n))
    (gm : Y.GoodAt (shiftG (T.Q.Dw j) a n (-c))) (g2 : Y.GoodAt (shiftG (T.Q.Dw j) a n (c + c))) (t : ℝ) (ht : 0 ≤ t)
    (hr : (Y.rk (shiftG (T.Q.Dw j) a n (c + c)) : ℝ) ≤ t * Y.rk (shiftG (T.Q.Dw j) a n (-c)))
    (S₀ S : Subgroup (LevelAut (T.Q.Dw j) Y.d.l₂))
    (h0 : ∃ u ∈ Y.V (wtOf (T.Q.Dw j) (c • hodgeWt (T.Q.Dw j)) 0), ∀ f ∈ secRing Y.d.Xo₂ Y.d.c₂,
      levDet Y.d.Xo₂ Y.d.c₂ S₀ u * f = 0 → f = 0)
    (h1 : ∃ u ∈ Y.V (wtOf (T.Q.Dw j) (c • hodgeWt (T.Q.Dw j)) 0), ∀ f ∈ secRing Y.d.Xo₂ Y.d.c₂,
      levDet Y.d.Xo₂ Y.d.c₂ S u * f = 0 → f = 0)
    (ρ : Representation ℂ (LevelAut (T.Q.Dw j) Y.d.l₂) (ℂ ⊗[Y.d.c₂.F] Y.V (wtZ a n)))
    (χ : LevelAut (T.Q.Dw j) Y.d.l₂ →* ℂˣ) (lam : S₀ →* ℂˣ)
    (hρ : ∀ (g : LevelAut (T.Q.Dw j) Y.d.l₂) (v w : Y.V (wtZ a n)), (w : Rul Y.d.Xo₂ Y.d.c₂) = transl Y.d.Xo₂ Y.d.c₂ g v →
      ρ g ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] v) = ((χ g : ℂˣ) : ℂ) • ((1 : ℂ) ⊗ₜ[Y.d.c₂.F] w)) :
    ∃ m : ℕ, EmbReg ρ S m ∧ (m : ℝ) * Nat.card S ≤ t * Nat.card S₀ * Module.finrank ℂ (eig ρ S₀ lam) := by
  have kp := fun G hG => (GlobalTheory.LevelIsometry.keeps_cusp_lattice_norm D T hL j hp1 hq1 hf hj Y e o hY G hG).1
  have hA : Y.d.l₂.A.Coprime Y.d.l₂.M := by rw [hY.lev.2]; exact Nat.coprime_one_left _
  rw [← (finrank_of_goodAt g2).2, ← (finrank_of_goodAt gm).2] at hr
  have a0 : shiftG (T.Q.Dw j) a n (-c) + wtOf (T.Q.Dw j) (c • hodgeWt (T.Q.Dw j)) 0 = wtZ a n := by
    rw [shiftG_add, neg_add_cancel, shiftG_zero']
  exact embReg_of_cusp (le_add_right hp1) hA Y.U (shiftG (T.Q.Dw j) a n (-c)) (wtZ a n) (shiftG (T.Q.Dw j) a n c)
    (shiftG (T.Q.Dw j) a n (c + c)) (wtOf (T.Q.Dw j) (c • hodgeWt (T.Q.Dw j)) 0) (even_shiftG _ _ hn _) (AllWt.even_wtOf _ _)
    a0 rfl (shiftG_add _ _ _ _ _) (kp _ (AllWt.even_wtOf _ _)) (kp _ ((Int.even_coe_nat _).2 hn)) (kp _ (even_shiftG _ _ hn _))
    (finrank_of_goodAt g0).1 (finrank_of_goodAt g2).1 t ht hr S₀ S h0 h1 ρ χ lam hρ


end GlobalTheory.BadEmb

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.CubicalProductIdentityOfGenericPointStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.UPoinc GlobalTheory.TorRef
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.USep
open GlobalTheory.Poinc.ThetaOne GlobalTheory.Poinc.Sep GlobalTheory.UT GlobalTheory.FieldBaseChange
open ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.Poinc.Sep.Frames GlobalTheory.UT.CoefBasic
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.cubicalProduct_identity_of_genericPoint : ∀ (V : Type) [CommRing V] [IsDomain V] (D : DegPre V) (N : ℕ) (b cχ : 𝟙_ (Over (Sp V)) ⟶ D.P.A),
    b ^ N = 1 → ∀ (χt : LB.Gen (LB.LinComb D.P.L ![(cχ * b).left, cχ.left, b.left, (η[D.P.A]).left] DegPre.gtε)),
    χt.IsGen →
    (∀ z J, Good D.P.L z J → ∏ i ∈ Finset.range N, cubV D.cub z J (toUnit (TF (R := V) (FractionRing V)) ≫ cχ)
        (toUnit (TF (R := V) (FractionRing V)) ≫ b ^ i) (toUnit (TF (R := V) (FractionRing V)) ≫ b) =
      val χt (toUnit (TF (R := V) (FractionRing V))).left z J ^ N) →
    ∀ (T : Over (Sp V)) (z : T.left) J, Good D.P.L z J →
      ∏ i ∈ Finset.range N, cubV D.cub z J (toUnit T ≫ cχ) (toUnit T ≫ b ^ i) (toUnit T ≫ b) = val χt T.hom z J ^ N := by
  first | exact @GlobalTheory.Poinc.Sep.CubInt.cubProd_of_generic | exact GlobalTheory.Poinc.Sep.CubInt.cubProd_of_generic | (intros; apply GlobalTheory.Poinc.Sep.CubInt.cubProd_of_generic <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DeRhamVectorExtension
section
namespace GlobalTheory

theorem deRhamVectorExtension : GlobalTheory.Published.DeRhamVectorExtension :=
  _root_.GlobalTheory.deRhamVectorExtension_of_abelianHodgeDeRham _root_.GlobalTheory.AbCoh.abelianHodgeDeRham

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DegenerationDataNsmulRescaleKeepsLawsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.degenerationDataNsmulRescale_keeps_laws : ∀ (R : Type) [CommRing R] [IsDomain R] (D : DegPre R) (O : Type) [CommRing O] [StarRing O] [Module O D.X] (oa : D.OAct O) (w0 : O) (n : ℕ), D.PsiEven → D.TauBimult → TraceFormTwistIso D oa w0 → (∀ y, PsiUnitOn D y Set.univ) → letI : Module O (mulDeg D n).X := ‹Module O D.X›; (mulDeg D n).PsiEven ∧ (mulDeg D n).TauBimult ∧ (∀ y, PsiUnitOn (mulDeg D n) y Set.univ) ∧ ∃ oa' : (mulDeg D n).OAct O, oa'.onB = oa.onB ∧ TraceFormTwistIso (mulDeg D n) oa' w0 := by
  first | exact @GlobalTheory.UCanon.MulDeg.mulDeg_laws | exact GlobalTheory.UCanon.MulDeg.mulDeg_laws | (intros; apply GlobalTheory.UCanon.MulDeg.mulDeg_laws <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DieudonneColengthEqLogDegree
section
open CategoryTheory TensorProduct Coalgebra Bialgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.Dieu

namespace GlobalTheory.Dieu

theorem length_quot_range_map_eq_of_hasLogDeg : ∀ (p : ℕ) [Fact p.Prime] (T : Theory p) (k : Type) [Field k]
    [CharP k p] [PerfectRing k p] (G H : PDivGroup p k) (q : G ⟶ H) (e : ℕ), IsIsog q → HasLogDeg q e →
    Module.length (WittVector p k) (T.M G ⧸ LinearMap.range (T.map q)) = e := by
  intro p _ T k _ _ _ G H q e hq he
  obtain ⟨n, g, hqg, hgq⟩ := hq
  have hq' : IsIsog q := ⟨n, g, hqg, hgq⟩
  have hg : IsIsog g := ⟨n, q, hgq, hqg⟩
  obtain ⟨e', he', -⟩ := _root_.GlobalTheory.Dieu.existsUnique_hasLogDeg p k H G g hg
  have hpG := ((_root_.GlobalTheory.Dieu.isog_basics p k G).1 n).2
  rw [← hqg] at hpG
  have hle : n * G.height ≤ e + e' := _root_.GlobalTheory.Dieu.hasLogDeg_comp_le p k G H G q g e e' _ he he' hpG
  have h1 := _root_.GlobalTheory.Dieu.le_length_coker_of_hasLogDeg p T k G H q e hq' he
  have h2 := _root_.GlobalTheory.Dieu.le_length_coker_of_hasLogDeg p T k H G g e' hg he'
  obtain ⟨hinj, hfin1, -⟩ := _root_.GlobalTheory.Dieu.isog_finrank_omega p T k G H q hq'
  obtain ⟨-, hfin2, -⟩ := _root_.GlobalTheory.Dieu.isog_finrank_omega p T k H G g hg
  obtain ⟨hid, hcomp, -, -, -, -, -, hrank, -⟩ :=
    _root_.GlobalTheory.Dieu.base_functor_props p (fun _ _ _ => True) T.base k G H G trivial trivial trivial
  obtain ⟨-, -, -, -, hsmulG, -⟩ :=
    _root_.GlobalTheory.Dieu.base_functor_props p (fun _ _ _ => True) T.base k G G G trivial trivial trivial
  obtain ⟨hadd, hpow, -⟩ := _root_.GlobalTheory.Dieu.colength_add_and_pow_and_eq p k (T.M G) (T.M H) (T.M G)
  have hsum := hadd (T.map q) (T.map g) hinj
  have hcomp' : T.map q ∘ₗ T.map g = T.map (q ≫ g) := (hcomp q g).symm
  have hmul : ∀ a : T.M G, (T.map q ∘ₗ T.map g) a = p ^ n • a := by
    intro a
    rw [hcomp', hqg]
    show T.base.map trivial trivial ((p : ℤ_[p]) ^ n • 𝟙 G) a = p ^ n • a
    rw [hsmulG n (𝟙 G) a, hid]
    rfl
  have hn := hpow (T.base.free G trivial) (T.base.finite G trivial) n _ hmul
  rw [hn, hrank] at hsum
  obtain ⟨a, ha⟩ := ENat.ne_top_iff_exists.mp hfin1
  obtain ⟨b, hb⟩ := ENat.ne_top_iff_exists.mp hfin2
  rw [← ha] at h1 hsum ⊢
  rw [← hb] at h2 hsum
  norm_cast at h1 h2 hsum ⊢
  omega

end GlobalTheory.Dieu
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualNumberPointsPulledBackObjectFromBase
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.UCanon.EpsPts

variable {S S₀ : Scheme.{0}}

theorem unit_hom (X : Scheme.{0}) : (𝟙_ (Over X)).hom = 𝟙 X := rfl

theorem exists_pt {G : Over S} {G₀ A : Over S₀} {g : S ⟶ S₀} {φ : G.left ⟶ G₀.left} {φB : G₀.left ⟶ A.left}
    (h₁ : IsPullback φ G.hom G₀.hom g) (h₂ : IsPullback φB G₀.hom A.hom (𝟙 S₀)) (a : S₀ ⟶ A.left)
    (ha : a ≫ A.hom = 𝟙 S₀) : ∃ x : S ⟶ G.left, x ≫ φ ≫ φB = g ≫ a ∧ x ≫ G.hom = 𝟙 S := by
  let P := h₂.lift (g ≫ a) g (by rw [Category.assoc, ha, Category.comp_id])
  refine ⟨h₁.lift P (𝟙 S) (by rw [h₂.lift_snd, Category.id_comp]), ?_, h₁.lift_snd _ _ _⟩
  rw [← Category.assoc, h₁.lift_fst, h₂.lift_fst]

theorem pt_unique {G : Over S} {G₀ A : Over S₀} {g : S ⟶ S₀} {φ : G.left ⟶ G₀.left} {φB : G₀.left ⟶ A.left}
    (h₁ : IsPullback φ G.hom G₀.hom g) (h₂ : IsPullback φB G₀.hom A.hom (𝟙 S₀)) {Z : Scheme.{0}} (r : Z ⟶ S)
    (x x' : Z ⟶ G.left) (hφ : x ≫ φ ≫ φB = x' ≫ φ ≫ φB) (hx : x ≫ G.hom = r) (hx' : x' ≫ G.hom = r) : x = x' := by
  apply h₁.hom_ext
  · apply h₂.hom_ext
    · simpa only [Category.assoc] using hφ
    · rw [Category.assoc, Category.assoc, h₁.w, ← Category.assoc, hx, ← Category.assoc, hx']
  · rw [hx, hx']

theorem pow_left {G : Over S} {G₀ A : Over S₀} [GrpObj G] [GrpObj G₀] [GrpObj A] {g : S ⟶ S₀}
    {φ : G.left ⟶ G₀.left} {φB : G₀.left ⟶ A.left}
    (h₁ : IsGrpPullback G G₀ g φ) (h₂ : IsGrpPullback G₀ A (𝟙 S₀) φB) (X : 𝟙_ (Over S) ⟶ G)
    (a : 𝟙_ (Over S₀) ⟶ A) (hX : X.left ≫ φ ≫ φB = g ≫ a.left) (n : ℕ) :
    (X ^ n).left ≫ φ ≫ φB = g ≫ (a ^ n).left := by
  let p₁ := pushHom h₁ (𝟙_ (Over S))
  let p₂ := pushHom h₂ (Over.mk ((𝟙_ (Over S)).hom ≫ g))
  let U : Over.mk (((𝟙_ (Over S)).hom ≫ g) ≫ 𝟙 S₀) ⟶ 𝟙_ (Over S₀) := toUnit _
  have hU : U.left = g := by
    have := Over.w U
    simpa [unit_hom] using this
  have e : p₂ (p₁ X) = preHom U a := by
    apply Over.OverMorphism.ext
    show (X.left ≫ φ) ≫ φB = U.left ≫ a.left
    rw [Category.assoc, hX, hU]
  have e' : p₂ (p₁ (X ^ n)) = preHom U (a ^ n) := by
    rw [map_pow, map_pow, e, map_pow]
  have := congrArg (fun z => z.left) e'
  rw [← Category.assoc]
  refine this.trans ?_
  show U.left ≫ (a ^ n).left = _
  rw [hU]

theorem c_nsmul {R : Type} [CommRing R] [IsDomain R] (D : DegPre R) (y : D.X) (n : ℕ) :
    D.c (n • y) = D.c y ^ n := by
  have hpadd : ∀ a b, D.c (a + b) = D.c a * D.c b := fun a b => by
    rw [D.c_add, Hom.mul_def]; rfl
  induction n with
  | zero =>
    have h := hpadd 0 0
    rw [add_zero] at h
    rw [zero_smul, pow_zero]
    exact (mul_eq_left.1 h.symm)
  | succ n ih => rw [succ_nsmul, hpadd, ih, pow_succ]

end GlobalTheory.UCanon.EpsPts

namespace GlobalTheory.UCanon


open GlobalTheory.UCanon.EpsPts in
theorem pts_eps_of_mul : ∀ {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {D' : Datum H} {l : Geo.Tor.Level H} {c : Coeff l} (L : LowBase D' c) (k : Type) [Field k] (f : L.W →+* DualNumber k) (o' : LowObj D' c (f.comp L.b)) (m₁ : ObjMap o' L.o (spMap f)) (m₂ : ObjMap o' L.o (spMap (GlobalTheory.RigChart.constHom f))) (n : ℕ), (n : k) ≠ 0 → (∀ (Z : Scheme.{0}) (x : Z ⟶ o'.t.G.left) (y : Z ⟶ Sp k), x ≫ o'.t.G.hom = y ≫ spMap (TrivSqZeroExt.fstHom k k k).toRingHom → x ≫ m₁.toSABMap.φ = x ≫ m₂.toSABMap.φ) → ∀ u : L.D.X → (Sp (DualNumber k) ⟶ o'.t.G.left), (∀ y, u y ≫ o'.t.G.hom = 𝟙 _) → (∀ y, u y ≫ m₁.toSABMap.φ ≫ L.φB = spMap f ≫ (L.D.c (n • y)).left) → (∀ y, u y ≫ m₂.toSABMap.φ ≫ L.φB = spMap (GlobalTheory.RigChart.constHom f) ≫ (L.D.c (n • y)).left) → ∃ x : L.D.X → (Sp (DualNumber k) ⟶ o'.t.G.left), (∀ y, x y ≫ m₁.toSABMap.φ ≫ L.φB = spMap f ≫ (L.D.c y).left) ∧ (∀ y, x y ≫ m₂.toSABMap.φ ≫ L.φB = spMap (GlobalTheory.RigChart.constHom f) ≫ (L.D.c y).left) ∧ (∀ y, x y ≫ o'.t.G.hom = 𝟙 _) := by
  intro E _ _ _ H D' l c L k _ f o' m₁ m₂ n hn h0 u hu hu₁ hu₂
  have hc : ∀ y, (L.D.c y).left ≫ L.D.P.A.hom = 𝟙 _ := fun y => Over.w (L.D.c y)
  have ex₁ := fun y => exists_pt m₁.cart.1 L.ab.1.1 (L.D.c y).left (hc y)
  have ex₂ := fun y => exists_pt m₂.cart.1 L.ab.1.1 (L.D.c y).left (hc y)
  choose x hx₁ hxG using ex₁
  choose x₂ hx₂ hx₂G using ex₂
  haveI : IsCommMonObj o'.t.G := o'.t.comm
  have hAb : IsAbelianScheme o'.t.G := ⟨o'.t.comm, o'.t.semi.smooth, o'.proper, o'.t.semi.geomConnected⟩
  let r : Sp k ⟶ Sp (DualNumber k) := spMap (TrivSqZeroExt.fstHom k k k).toRingHom
  have hr : r ≫ spMap f = r ≫ spMap (GlobalTheory.RigChart.constHom f) := by
    simp only [r, spMap, ← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    all_goals (ext z; simp [GlobalTheory.RigChart.constHom])
  have heq : ∀ y, x y = x₂ y := by
    intro y
    let X : 𝟙_ (Over (Sp (DualNumber k))) ⟶ o'.t.G := Over.homMk (x y) (hxG y)
    let X₂ : 𝟙_ (Over (Sp (DualNumber k))) ⟶ o'.t.G := Over.homMk (x₂ y) (hx₂G y)
    have hpow : X ^ n = X₂ ^ n := by
      apply Over.OverMorphism.ext
      have e₁ : (X ^ n).left = u y := by
        apply pt_unique m₁.cart.1 L.ab.1.1 (𝟙 _) _ _ _ (Over.w (X ^ n)) (hu y)
        rw [pow_left m₁.cart L.ab.1 X (L.D.c y) (hx₁ y) n, hu₁ y, c_nsmul]
      have e₂ : (X₂ ^ n).left = u y := by
        apply pt_unique m₂.cart.1 L.ab.1.1 (𝟙 _) _ _ _ (Over.w (X₂ ^ n)) (hu y)
        rw [pow_left m₂.cart L.ab.1 X₂ (L.D.c y) (hx₂ y) n, hu₂ y, c_nsmul]
      rw [e₁, e₂]
    have h0' : r ≫ X.left = r ≫ X₂.left := by
      show r ≫ x y = r ≫ x₂ y
      have hh := h0 (Sp k) (r ≫ x₂ y) (𝟙 _) (by rw [Category.assoc, hx₂G, Category.comp_id, Category.id_comp])
      have hh' : r ≫ x₂ y ≫ m₁.cm.F = r ≫ x₂ y ≫ m₂.cm.F := by simpa only [Category.assoc] using hh
      have w₁ : x y ≫ m₁.cm.F ≫ L.o.t.G.hom = spMap f := by
        rw [m₁.cart.1.w, ← Category.assoc, hxG y, Category.id_comp]
      have w₂ : x₂ y ≫ m₂.cm.F ≫ L.o.t.G.hom = spMap (GlobalTheory.RigChart.constHom f) := by
        rw [m₂.cart.1.w, ← Category.assoc, hx₂G y, Category.id_comp]
      apply m₁.cart.1.hom_ext
      · simp only [Category.assoc]
        rw [hh']
        apply L.ab.1.1.hom_ext
        · simp only [Category.assoc]
          rw [hx₁ y, hx₂ y, ← Category.assoc, hr, Category.assoc]
        · simp only [Category.assoc]
          rw [w₁, w₂, hr]
      · simp only [Category.assoc]
        rw [hxG y, hx₂G y]
    exact congrArg (fun z => z.left) (eq_of_pow_eq_of_eq_at_closed k o'.t.G hAb n hn X X₂ hpow h0')
  exact ⟨x, hx₁, fun y => heq y ▸ hx₂ y, hxG⟩

end GlobalTheory.UCanon
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfMumfordBundleTorsionPresentationsStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.UChart GlobalTheory.UCanon GlobalTheory.PolDeg GlobalTheory.TInj
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.eq_of_mumfordBundle_torsion_presentations : ∀ (V : Type) [CommRing V] [IsDomain V] [CharZero V] (D : DegPre V) {S : Scheme.{0}} (B : Over S) [GrpObj B] [IsCommMonObj B] (P : LB (G2 B).left), P.IsLB → ∀ (t : Sp V ⟶ S) (a₁ a₂ : D.P.A.left ⟶ B.left) (aa₁ aa₂ : (G2 D.P.A).left ⟶ (G2 B).left), IsGrpPullback D.P.A B t a₁ → IsGrpPullback D.P.A B t a₂ → IsSquare a₁ aa₁ → IsSquare a₂ aa₂ → LBIso (abelian₂ D.P.A D.P.L) (P.pull aa₁) → LBIso (abelian₂ D.P.A D.P.L) (P.pull aa₂) → ∀ n : ℕ, 3 ≤ n → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing V) F], (∀ x : TF (R := V) F ⟶ D.P.A, x ^ n = 1 → x.left ≫ a₁ = x.left ≫ a₂) → a₁ = a₂ := by
  first | exact @GlobalTheory.PresRigid.eq_of_lam_of_torsion | exact GlobalTheory.PresRigid.eq_of_lam_of_torsion | (intros; apply GlobalTheory.PresRigid.eq_of_lam_of_torsion <;> assumption)
end

