module

public import Formalism.LocalToGlobal.KernelLattices.EntryG
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ColInst
public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.ColInst
public import Formalism.LocalToGlobal.Columns.ChainInstY
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerEquivFr
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.Bundle0001
public import Formalism.LocalToGlobal.KernelLattices.Bundle0005
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.JetsRationalOfKernelRationality

@[expose] public section

-- bundled from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.EntryG
section
noncomputable section
open scoped BigOperators ComplexConjugate
open NumberField IsDedekindDomain MvPolynomial

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H
open Formalism.L2.AlgTh (KerStd SplitS)
open Formalism.L2.AtG.EntryG (IsEntryG Term isEntryG_zero)
open Formalism.DivisionValues (vw)

section Tower

variable {E : Type} [Field E] [NumberField E] {H M : Type} [AddCommGroup H] [Module (𝓞 E) H] [AddCommMonoid M]

def lrep (A B : Submodule (𝓞 E) H) (z : ↥A ⧸ B.comap A.subtype) : ↥A :=
  Function.surjInv (Submodule.Quotient.mk_surjective (B.comap A.subtype)) z

theorem latSum_eq (A B : Submodule (𝓞 E) H) (F : H → M) : latSum A B F = ∑ᶠ z, F (lrep A B z : H) := rfl

theorem mk_lrep (A B : Submodule (𝓞 E) H) (z : ↥A ⧸ B.comap A.subtype) : Submodule.Quotient.mk (lrep A B z) = z :=
  Function.surjInv_eq _ z

theorem lrep_mk_sub (A B : Submodule (𝓞 E) H) (a : ↥A) :
    ((lrep A B (Submodule.Quotient.mk a) : ↥A) : H) - (a : H) ∈ B := by
  have h := mk_lrep A B (Submodule.Quotient.mk a)
  rw [Submodule.Quotient.eq] at h
  simpa using h

theorem latSum_congr (A B : Submodule (𝓞 E) H) {F G : H → M} (h : ∀ x ∈ A, F x = G x) : latSum A B F = latSum A B G := by
  rw [latSum_eq, latSum_eq]
  exact finsum_congr fun z => h _ (lrep A B z).2

theorem latSum_tower (A B C : Submodule (𝓞 E) H) (hCB : C ≤ B) (hBA : B ≤ A) (F : H → M)
    (hF : ∀ x c, c ∈ C → F (x + c) = F x) [Finite (↥A ⧸ C.comap A.subtype)] :
    latSum A C F = latSum A B fun x => latSum B C fun y => F (x + y) := by
  classical
  let φ : (↥A ⧸ B.comap A.subtype) × (↥B ⧸ C.comap B.subtype) → (↥A ⧸ C.comap A.subtype) := fun zt =>
    Submodule.Quotient.mk ⟨(lrep A B zt.1 : H) + (lrep B C zt.2 : H), A.add_mem (lrep A B zt.1).2 (hBA (lrep B C zt.2).2)⟩
  have hinj : Function.Injective φ := by
    rintro ⟨z, t⟩ ⟨z', t'⟩ h
    have h1 : ((lrep A B z : H) + (lrep B C t : H)) - ((lrep A B z' : H) + (lrep B C t' : H)) ∈ C := by
      have h0 := (Submodule.Quotient.eq _).1 h
      simpa using h0
    have hz : z = z' := by
      rw [← mk_lrep A B z, ← mk_lrep A B z', Submodule.Quotient.eq]
      show ((lrep A B z - lrep A B z' : ↥A) : H) ∈ B
      have e : ((lrep A B z - lrep A B z' : ↥A) : H) =
          (((lrep A B z : H) + (lrep B C t : H)) - ((lrep A B z' : H) + (lrep B C t' : H))) - (lrep B C t : H) + (lrep B C t' : H) := by
        push_cast
        abel
      rw [e]
      exact B.add_mem (B.sub_mem (hCB h1) (lrep B C t).2) (lrep B C t').2
    subst hz
    have ht : t = t' := by
      rw [← mk_lrep B C t, ← mk_lrep B C t', Submodule.Quotient.eq]
      show ((lrep B C t - lrep B C t' : ↥B) : H) ∈ C
      have e : ((lrep B C t - lrep B C t' : ↥B) : H) =
          ((lrep A B z : H) + (lrep B C t : H)) - ((lrep A B z : H) + (lrep B C t' : H)) := by
        push_cast
        abel
      rw [e]
      exact h1
    rw [ht]
  have hsurj : Function.Surjective φ := by
    intro w
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ w
    have hb : (a : H) - (lrep A B (Submodule.Quotient.mk a) : H) ∈ B := by
      have := B.neg_mem (lrep_mk_sub A B a)
      simpa using this
    refine ⟨(Submodule.Quotient.mk a, Submodule.Quotient.mk ⟨_, hb⟩), ?_⟩
    show Submodule.Quotient.mk _ = Submodule.Quotient.mk a
    rw [Submodule.Quotient.eq]
    have h2 := lrep_mk_sub B C ⟨_, hb⟩
    show (lrep A B (Submodule.Quotient.mk a) : H) + (lrep B C (Submodule.Quotient.mk ⟨_, hb⟩) : H) - (a : H) ∈ C
    have e : (lrep A B (Submodule.Quotient.mk a) : H) + (lrep B C (Submodule.Quotient.mk ⟨_, hb⟩) : H) - (a : H) =
        (lrep B C (Submodule.Quotient.mk ⟨_, hb⟩) : H) - ((a : H) - (lrep A B (Submodule.Quotient.mk a) : H)) := by abel
    rw [e]
    exact h2
  have hG : ∀ a : ↥A, F (lrep A C (Submodule.Quotient.mk a) : H) = F a := by
    intro a
    have h := hF (a : H) _ (lrep_mk_sub A C a)
    rwa [add_sub_cancel] at h
  have : Finite ((↥A ⧸ B.comap A.subtype) × (↥B ⧸ C.comap B.subtype)) := Finite.of_injective φ hinj
  have : Finite (↥A ⧸ B.comap A.subtype) := Finite.prod_left (↥B ⧸ C.comap B.subtype)
  have : Finite (↥B ⧸ C.comap B.subtype) := Finite.prod_right (↥A ⧸ B.comap A.subtype)
  let _ := Fintype.ofFinite (↥A ⧸ C.comap A.subtype)
  let _ := Fintype.ofFinite (↥A ⧸ B.comap A.subtype)
  let _ := Fintype.ofFinite (↥B ⧸ C.comap B.subtype)
  simp only [latSum_eq, finsum_eq_sum_of_fintype]
  rw [← (Function.Bijective.sum_comp ⟨hinj, hsurj⟩ fun w => F (lrep A C w : H)), Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun z _ => Finset.sum_congr rfl fun t _ => ?_
  exact hG _

theorem latSum_mul_left {R : Type} [NonUnitalNonAssocSemiring R] (A B : Submodule (𝓞 E) H) [Finite (↥A ⧸ B.comap A.subtype)] (r : R) (F : H → R) :
    latSum A B (fun x => r * F x) = r * latSum A B F := by
  let _ := Fintype.ofFinite (↥A ⧸ B.comap A.subtype)
  rw [latSum_eq, latSum_eq, finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, Finset.mul_sum]

theorem mulLat_mul_le (c k : ℕ) (M : Submodule (𝓞 E) H) : mulLat (c * k) M ≤ mulLat c M := by
  intro w hw
  obtain ⟨y, hy, rfl⟩ := (mem_mulLat (c * k) M w).1 hw
  refine (mem_mulLat c M _).2 ⟨(k : 𝓞 E) • y, M.smul_mem _ hy, ?_⟩
  rw [smul_smul, Nat.cast_mul]

theorem mulLat_le_divLat (c d : ℕ) (M : Submodule (𝓞 E) H) : mulLat c M ≤ divLat d M := by
  intro w hw
  obtain ⟨y, hy, rfl⟩ := (mem_mulLat c M w).1 hw
  exact (mem_divLat d M _).2 (M.smul_mem _ (M.smul_mem _ hy))

end Tower

section Regroup

variable {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E)))
  (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b))

theorem fin_div (hN : IsSdLat N) (hN' : IsSdLat N') (cA c : ℕ) (hA : 0 < cA) (hc : 0 < c) :
    Finite (↥(divLat cA (homAt S N N')) ⧸ (mulLat c (homAt S N N')).comap (divLat cA (homAt S N N')).subtype) :=
  kerFin S N N' hN hN' cA c hA hc

theorem fin_mul (hN : IsSdLat N) (hN' : IsSdLat N') (c c' : ℕ) (hc : 0 < c) (hc' : 0 < c') :
    Finite (↥(mulLat c (homAt S N N')) ⧸ (mulLat (c * c') (homAt S N N')).comap (mulLat c (homAt S N N')).subtype) :=
  lattice_classes_finite_refinement X a b S N N' c c' hN hN' hc hc'

end Regroup

section Cf

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

end Cf

section LatSum

variable {E : Type} [Field E] [NumberField E] {H : Type} [AddCommGroup H] [Module (𝓞 E) H]

end LatSum

section Clo

variable {X : Fields} {p : ℕ} [Fact p.Prime] {a b : ℕ} {A : Amb X} {a₀ : ℕ} {b₀ c₀' : ℤ} {ha : 0 < a₀} {hd : 0 < A.d} {lam₀ : ℂ}
  {hlam : lam₀ ≠ 0} {ι : ℂ ≃+* ℂ_[p]} {ϖ : ℂ} {pE : 𝓞 X.E} {D : ℕ} {e : ℝ}

end Clo

section Entry

variable {X : Fields} {p : ℕ} [Fact p.Prime] {a b : ℕ} (A : Amb X) (a₀ : ℕ) (b₀ c₀' : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam₀ : ℂ)
  (hlam : lam₀ ≠ 0) (ι : ℂ ≃+* ℂ_[p]) (ϖ : ℂ) (pE : 𝓞 X.E) (D : ℕ) (e : ℝ)

end Entry

section Rec

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {Sg : Set ℕ}
  (mu : Tup X.F X.E X.K Sg) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) {p : ℕ} [Fact p.Prime] (a₀ : ℕ) (b₀ c₀' : ℤ) (ha : 0 < a₀) (hd : 0 < A.d) (lam₀ : ℂ)
  (hlam : lam₀ ≠ 0) (ι : ℂ ≃+* ℂ_[p]) (ϖ : ℂ) (pE : 𝓞 X.E) (D : ℕ) (e : ℝ) {u : Pr.Word} (m2 : ℕ)

end Rec

section Deg

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {a b : ℕ}

end Deg

section Lat

variable {X : Fields} (A : Amb X) {p : ℕ} [Fact p.Prime] {a b : ℕ}

end Lat

namespace Test

end Test

end Formalism.L2.Ker
end
end

-- bundled from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ModulusDivPrimePowIntegralBad
section
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col

section Helpers

variable {X : Fields} {Pr : Primes X} {R : Ranks}
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu))




end Helpers

section Alg

end Alg

section Inv1

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  {u : Pr.Word}





end Inv1

section Cp1Thm

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ)

end Cp1Thm

end Formalism.L2.Ker
end
end

-- bundled from Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.RatKDeg
section
open NumberField IsDedekindDomain

noncomputable section

namespace Formalism.L2.Ker

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Th1.H Formalism.MainNotions

theorem natW_cast {n : ℕ} (lam : DomWeight n) (i : Fin n) : ((lam.natW i : ℕ) : ℤ) = lam.w i - lam.detShift := by
  unfold DomWeight.natW
  have h : lam.detShift ≤ lam.w i := by
    unfold DomWeight.detShift
    have hn : 0 < n := Fin.pos i
    rw [dif_pos hn]
    exact lam.anti (show i ≤ ⟨n - 1, by omega⟩ from Fin.mk_le_mk.2 (by omega))
  omega

theorem chain_degree_eq : StepDegIs := by
  intro X Pr R W u i hi τ
  unfold stepDeg opDeg
  push_cast
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [natW_cast, nuLast_eq W u i hi τ]
  have hN : 0 < R.N i := R.N_pos i
  have d0 : (W.lamTrue u i τ).detShift = (W.lamTrue u i τ).w ⟨R.N i - 1, by omega⟩ := by
    unfold DomWeight.detShift
    exact dif_pos hN
  have d1 : (W.nuW u (i + 1) τ).detShift = (W.nuW u (i + 1) τ).w ⟨R.N i - 1, by show R.N i - 1 < R.N i; omega⟩ := by
    unfold DomWeight.detShift
    exact dif_pos hN
  rw [d0, d1]
  show (W.lamN u i τ).w r + _ - ((W.lamN u i τ).w _ + _) + ((W.lamN u i τ).w _ + _) = (W.lamN u i τ).w r + _
  ring

section Op

variable {K : Type} [Field K] [Infinite K] {ι : Type} [Fintype ι] {a b : ℕ}

theorem jetOp_congr (lam : ι → DomWeight a) (lam' : ι → DomWeight b) (n : ι → ℕ) (J J' : (DVar ι a b →₀ ℕ) → K)
    (h : ∀ m, (∀ τ, degAt m τ = opDeg lam n τ) → J m = J' m) : jetOp lam lam' J n = jetOp lam lam' J' n := by
  ext P
  unfold jetOp
  simp only [LinearMap.comp_apply, Submodule.subtype_apply]
  rw [jet_local_rationality K ι a b lam n J J' h P P.2]

end Op

section Props

variable {X : Fields} (A : Amb X) {a b : ℕ} (Sall SB : Finset (HeightOneSpectrum (𝓞 X.E))) (D : ℕ)

theorem jetK_spec_deg (dg : X.Tau → ℕ) (hrat : A.JetsRatDeg a b Sall D dg) (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ)
    (x : HomE X.E a b) (hR : InRange Sall D c N N' x) (m : DVar X.Tau a b →₀ ℕ) (hm : ∀ τ, degAt m τ = dg τ) :
    A.σ₀ (A.jetK Sall N N' c x m) = (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' c x) m := by
  obtain ⟨k, hk⟩ := hrat N N' c x hR m hm
  unfold Amb.jetK
  rw [← hk, desc_map]

theorem jetAddDeg_of (dg : X.Tau → ℕ) (hfin : LatFin (X := X) a b Sall) (hadd : A.IndAdd a b Sall D) (hsm : A.IndSmooth a b Sall D)
    (hrat : A.JetsRatDeg a b Sall D dg) : A.JetAddDeg a b Sall D dg := by
  intro N N' c c' x hc hc' hR m hm
  have := hfin N N' c c' hR.1 hR.2.1 hc hc'
  let _ := Fintype.ofFinite (↥(mulLat c (homAt Sall N N')) ⧸ (mulLat (c * c') (homAt Sall N N')).comap (mulLat c (homAt Sall N N')).subtype)
  unfold latSum
  rw [finsum_eq_sum_of_fintype]
  set rep := fun z : ↥(mulLat c (homAt Sall N N')) ⧸ (mulLat (c * c') (homAt Sall N N')).comap (mulLat c (homAt Sall N N')).subtype =>
    ((Function.surjInv (Submodule.Quotient.mk_surjective ((mulLat (c * c') (homAt Sall N N')).comap (mulLat c (homAt Sall N N')).subtype)) z :
      ↥(mulLat c (homAt Sall N N'))) : HomE X.E a b) with hrep
  have hRz : ∀ z, InRange Sall D (c * c') N N' (x + rep z) := fun z => hR.add (Subtype.coe_prop _)
  have h1 : A.thInd Sall N N' c x = fun w => ∑ z, A.thInd Sall N N' (c * c') (x + rep z) w := by
    funext w
    rw [hadd N N' c c' x hc hc' hR w]
    unfold latSum
    rw [finsum_eq_sum_of_fintype]
  have h2 : derivAt0 (A.thInd Sall N N' c x) m = ∑ z, derivAt0 (A.thInd Sall N N' (c * c') (x + rep z)) m := by
    unfold derivAt0
    rw [h1, iteratedFDeriv_sum (fun z _ => hsm N N' (c * c') (x + rep z) (hRz z) _)]
    rw [Finset.sum_apply, _root_.sum_apply]
  choose k hk using fun z => hrat N N' (c * c') (x + rep z) (hRz z) m hm
  have h3 : (A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' c x) m = A.σ₀ (∑ z, k z) := by
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum]
    simp only [hk]
    unfold jetC
    rw [h2, Finset.mul_sum, Finset.mul_sum]
  unfold Amb.jetK
  rw [h3, desc_map]
  refine Finset.sum_congr rfl fun z _ => ?_
  show k z = desc A.σ₀ ((A.chiF a b N N')⁻¹ * jetC A.cD (A.thInd Sall N N' (c * c') (x + rep z)) m)
  rw [← hk z, desc_map]

variable (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) (mU : HeightOneSpectrum (𝓞 X.E) → X.Kˣ) (mI : SB → X.E → X.K)
  (lam : X.Tau → DomWeight a) (lam' : X.Tau → DomWeight b) (n : X.Tau → ℕ)

theorem thDistC_add_deg (hfin : LatFin (X := X) a b Sall) (hadd : A.JetAddDeg a b Sall D (opDeg lam n))
    (N : Submodule (𝓞 X.E) (Sp X.E a)) (fr : Frs X.E a SB) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (fr' : Frs X.E b SB)
    (c c' : ℕ) (x : HomE X.E a b) (hc : 0 < c) (hc' : 0 < c') (hR : InRange Sall D (c * c') N N' x) :
    thDistC A Sall SB D sel mU mI lam lam' n N fr N' fr' c x =
      latSum (mulLat c (homAt Sall N N')) (mulLat (c * c') (homAt Sall N N')) fun y =>
        thDistC A Sall SB D sel mU mI lam lam' n N fr N' fr' (c * c') (x + y) := by
  have := hfin N N' c c' hR.1 hR.2.1 hc hc'
  let _ := Fintype.ofFinite (↥(mulLat c (homAt Sall N N')) ⧸ (mulLat (c * c') (homAt Sall N N')).comap (mulLat c (homAt Sall N N')).subtype)
  have hJ : jetOp lam lam' (A.jetK Sall N N' c x) n = jetOp lam lam' (fun m => ∑ z : ↥(mulLat c (homAt Sall N N')) ⧸ (mulLat (c * c') (homAt Sall N N')).comap (mulLat c (homAt Sall N N')).subtype,
      A.jetK Sall N N' (c * c') (x + ((Function.surjInv (Submodule.Quotient.mk_surjective
        ((mulLat (c * c') (homAt Sall N N')).comap (mulLat c (homAt Sall N N')).subtype)) z : ↥(mulLat c (homAt Sall N N'))) : HomE X.E a b)) m) n := by
    refine jetOp_congr lam lam' n _ _ fun m hm => ?_
    rw [hadd N N' c c' x hc hc' hR m hm]
    unfold latSum
    rw [finsum_eq_sum_of_fintype]
  unfold latSum
  rw [finsum_eq_sum_of_fintype]
  unfold thDistC
  rw [if_pos ⟨(Dvd.intro _ rfl).trans hR.2.2.2.1, hR.2.2.2.2⟩, hJ, jetOp_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun z _ => ?_
  exact (if_pos ⟨hR.2.2.2.1, mem_divLat_add D c _ hR.2.2.2.2 (Subtype.coe_prop _)⟩).symm

theorem thDistC_ok_deg (hD : 0 < D) (rho : UF X.E a →* Module.End X.K (DIV.VV X.K lam)) (rho' : UF X.E b →* Module.End X.K (DIV.VV X.K lam'))
    (sS sT : SB → X.E → X.K) (hfin : LatFin (X := X) a b Sall) (hadd : A.JetAddDeg a b Sall D (opDeg lam n))
    (heq : ThEquivP (thDistC A Sall SB D sel mU mI lam lam' n) Sall D rho rho')
    (ha : MuDetLaw a mI sS) (hb : MuDetLaw b mI sS) (hi : UnitInv sS sT) :
    ThDist.Ok (thDistC A Sall SB D sel mU mI lam lam' n) Sall D rho rho' sS sT :=
  { cong := fun N fr N' fr' c x x' _ _ h => thDistC_cong A Sall SB sel mU mI lam lam' n D N fr N' fr' c x x' h
    add := fun N fr N' fr' c c' x hN hN' hc hc' hd hx =>
      thDistC_add_deg A Sall SB D sel mU mI lam lam' n hfin hadd N fr N' fr' c c' x hc hc' ⟨hN, hN', Nat.mul_pos hc hc', hd, hx⟩
    equiv := thDistC_equiv A Sall SB sel mU mI lam lam' n D hD rho rho' heq
    det := fun N fr N' fr' c x κ κ' _ _ => thDistC_det A Sall SB sel mU mI lam lam' n D sS sT ha hb hi N fr N' fr' c x κ κ' }

end Props

section Chain

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K)))
  (A : Amb X) (u : Pr.Word) (m2 : ℕ)

theorem jetAddDeg_of_ana {a b : ℕ} {Sall : Finset (HeightOneSpectrum (𝓞 X.E))} {D : ℕ} {dg : X.Tau → ℕ} (hD : 0 < D) (h : A.AnaStepD a b Sall D dg) :
    A.JetAddDeg a b Sall D dg :=
  jetAddDeg_of A Sall D dg (lattice_classes_finite_refinement X a b Sall) (indAdd_of A a b Sall D hD (lattice_classes_finite_refinement X a b Sall) (indTieD_of_la A a b Sall D hD h.1))
    (indSmooth_of A _ _ _ _ h.2.1) h.2.2

theorem stepC_ok_deg (i : ℕ) (hi : i < R.m) {b : ℕ} (lam' : X.Tau → DomWeight b) (hT : 0 < Pr.T u)
    (rho : UF X.E (R.N i) →* Module.End X.K (DIV.VV X.K (W.lamTrue u i))) (rho' : UF X.E b →* Module.End X.K (DIV.VV X.K lam'))
    (hq : MuqTie Ch sel mu cst)
    (hs : A.AnaStepD (R.N i) b (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) (stepDeg W u i))
    (heqT : ThEquivP (stepT W Ch sel mu cst A u i lam') (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) rho rho') :
    ThDist.Ok (stepC W Ch sel mu cst A u i lam') (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) rho rho'
      (rhoS Ch sel mu i) (rhoT Ch sel mu i) :=
  have heq : ThEquivP (stepC W Ch sel mu cst A u i lam') (Sall sel mu u) (cAof sel mu cst * cBof sel mu cst u) rho rho' := by
    rw [stepC_eq_stepT W Ch sel mu cst hq A u i hi lam']; exact heqT
  thDistC_ok_deg A (Sall sel mu u) (rowSG Pr sel mu) _ sel (mUof Ch mu i) (muAt Ch sel mu cst i) (W.lamTrue u i) lam' (nuLast W u i)
    (modulus_pos sel mu cst u hT) rho rho' _ _ (lattice_classes_finite_refinement X _ _ _)
    (jetAddDeg_of_ana A (modulus_pos sel mu cst u hT) hs) heq
    (muDetLaw_chain Ch sel mu cst i _) (muDetLaw_chain Ch sel mu cst i _) (unitInv_rho Ch sel mu i)

theorem chTh_ok_ambD (hm : m2 + 1 < R.m) (hT : 0 < Pr.T u) (hq : MuqTie Ch sel mu cst) (h : ThHypD W Ch sel mu cst A u m2) :
    ChTh.Ok (Ch := Ch) cst (chTh W Ch sel mu cst A u m2) :=
  { th i hi := stepC_ok_deg W Ch sel mu cst A u i (by omega) _ hT _ _ hq (h.1 i hi) (h.2.2.1 i hi)
    top := stepC_ok_deg W Ch sel mu cst A u (m2 + 1) hm _ hT _ _ hq h.2.1 h.2.2.2 }

end Chain

section ChainN

variable {X : Fields} {Pr : Primes X} {R : Ranks} (W : Wts X Pr.Word R) (Ch : Chars X Pr R.m)
  (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ}
  (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m)
  {D : D7} (s : Seam D X) {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} (B : Base D cc δ) (χ : TaylorLogMetric.IdE D → ℂ) (cD : D.what₂.Tau → ℂ) (u : Pr.Word) (m2 : ℕ)

end ChainN



end Formalism.L2.Ker
end
end

