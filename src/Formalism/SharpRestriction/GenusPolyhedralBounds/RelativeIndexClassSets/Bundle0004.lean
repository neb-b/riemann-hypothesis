module

public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0002
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.Bundle0001
public import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.LevelsQDesc

@[expose] public section

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.ExistsGlobalFamilyQuotientBounded
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

section LinAlgQ

theorem exists_den {R K V : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (M : Submodule R V)
    (hM : Submodule.span K (M : Set V) = ⊤) (v : V) : ∃ s ∈ nonZeroDivisors R, s • v ∈ M := by
  have hv : v ∈ Submodule.span K (M : Set V) := by rw [hM]; trivial
  induction hv using Submodule.span_induction with
  | mem x hx => exact ⟨1, one_mem _, by rwa [one_smul]⟩
  | zero => exact ⟨1, one_mem _, by rw [smul_zero]; exact M.zero_mem⟩
  | add x y _ _ hx hy =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨t, ht, hty⟩ := hy
    refine ⟨s * t, mul_mem hs ht, ?_⟩
    have h1 : (s * t) • x = t • (s • x) := by rw [mul_comm, mul_smul]
    rw [smul_add, h1, mul_smul]
    exact M.add_mem (M.smul_mem _ hsx) (M.smul_mem _ hty)
  | smul a x _ hx =>
    obtain ⟨s, hs, hsx⟩ := hx
    obtain ⟨n, d, hd, rfl⟩ := IsFractionRing.div_surjective R a
    refine ⟨d * s, mul_mem hd hs, ?_⟩
    have hd0 : algebraMap R K d ≠ 0 :=
      (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (nonZeroDivisors.ne_zero hd)
    have h1 : (d * s) • ((algebraMap R K n / algebraMap R K d) • x) = n • (s • x) := by
      rw [← algebraMap_smul K (d * s), ← algebraMap_smul K n, ← algebraMap_smul K s, smul_smul, smul_smul, map_mul]
      congr 1
      field_simp
    rw [h1]
    exact M.smul_mem _ hsx

theorem finrank_quot_eq {R K V : Type*} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
    [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V] (M : Submodule R V)
    (hM : Submodule.span K (M : Set V) = ⊤) (W : Submodule K V) :
    finrank R (M ⧸ (W.restrictScalars R).comap M.subtype) = finrank K (V ⧸ W) := by
  let g : M →ₗ[R] (V ⧸ W) := (W.mkQ.restrictScalars R).comp M.subtype
  have hker : LinearMap.ker g = (W.restrictScalars R).comap M.subtype := by
    ext x
    simp [g]
  let f : (M ⧸ (W.restrictScalars R).comap M.subtype) →ₗ[R] (V ⧸ W) :=
    Submodule.liftQ _ g (le_of_eq hker.symm)
  have hinj : Function.Injective f := by
    rw [← LinearMap.ker_eq_bot]
    exact Submodule.ker_liftQ_eq_bot _ _ _ (le_of_eq hker)
  have hloc : IsLocalizedModule (nonZeroDivisors R) f := by
    refine ⟨fun s => ?_, fun y => ?_, fun {x₁ x₂} h => ⟨1, by rw [hinj h]⟩⟩
    · have hs0 : algebraMap R K s ≠ 0 :=
        (map_ne_zero_iff _ (IsFractionRing.injective R K)).mpr (nonZeroDivisors.ne_zero s.2)
      rw [Module.End.isUnit_iff]
      constructor
      · intro a b hab
        simp only [Module.algebraMap_end_apply] at hab
        rw [← algebraMap_smul K (s : R) a, ← algebraMap_smul K (s : R) b] at hab
        exact smul_right_injective _ hs0 hab
      · intro a
        refine ⟨(algebraMap R K s)⁻¹ • a, ?_⟩
        simp only [Module.algebraMap_end_apply]
        rw [← algebraMap_smul K (s : R), smul_smul, mul_inv_cancel₀ hs0, one_smul]
    · obtain ⟨v, rfl⟩ := W.mkQ_surjective y
      obtain ⟨s, hs, hsv⟩ := exists_den (K := K) M hM v
      refine ⟨(Submodule.Quotient.mk ⟨s • v, hsv⟩, ⟨s, hs⟩), ?_⟩
      rfl
  rw [IsLocalization.finrank_eq K (nonZeroDivisors R) le_rfl, IsLocalizedModule.finrank_eq (nonZeroDivisors R) f le_rfl]

theorem exists_sub_basis {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    (Sh : Finset V) (hS : Submodule.span K (Sh : Set V) = ⊤) (W : Submodule K V) :
    ∃ e : Fin (finrank K (V ⧸ W)) → V, (∀ i, e i ∈ Sh) ∧ Submodule.span K (Set.range e) ⊔ W = ⊤ := by
  classical
  obtain ⟨b, hb, hspan, hli⟩ := exists_linearIndependent K (W.mkQ '' (Sh : Set V))
  have htop : Submodule.span K b = ⊤ := by
    rw [hspan, Submodule.span_image, hS, Submodule.map_top, Submodule.range_mkQ]
  have hfin : Finite b := ((Sh.finite_toSet.image _).subset hb).to_subtype
  have := Fintype.ofFinite b
  let bs : Basis b K (V ⧸ W) := Basis.mk hli (by rw [Subtype.range_coe, htop])
  have hcard : Fintype.card b = finrank K (V ⧸ W) := (finrank_eq_card_basis bs).symm
  let eq : Fin (finrank K (V ⧸ W)) ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  have hpre : ∀ k, ∃ v ∈ (Sh : Set V), W.mkQ v = (eq k : V ⧸ W) := fun k => hb (eq k).2
  choose e he1 he2 using hpre
  refine ⟨e, fun i => he1 i, ?_⟩
  rw [sup_comm, ← Submodule.map_mkQ_eq_top, Submodule.map_span, ← Set.range_comp]
  have : (⇑W.mkQ ∘ e) = (Subtype.val : b → V ⧸ W) ∘ eq := by funext k; exact he2 k
  rw [this, Set.range_comp, eq.surjective.range_eq, Set.image_univ, Subtype.range_coe, htop]

end LinAlgQ

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

theorem rhoP_eq_finrank (B : WeightFamilies.Prov D) (CR T c : ℝ) (j : ℕ) (ka : WeightFamilies.Wt D j)
    (hM : Submodule.span B.KO (B.Mlat j ka : Set (B.Cusp j ka)) = ⊤) :
    WeightFamilies.rhoP B CR T c j ka = finrank B.KO (B.Cusp j ka ⧸ WeightFamilies.MggK B CR T c j ka) :=
  finrank_quot_eq (B.Mlat j ka) hM (WeightFamilies.MggK B CR T c j ka)

theorem exists_global_family_quotient_bounded {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G0 : GlobalFamilyData X ka wL wF) (large₂ : SizeData₂ D) (S : Scal B)
    (CRm : ℝ) (T : ℕ) (c be Ch Ah : ℝ)
    (hS4 : ShortG X ka (X.Thc S.sK ka) be)
    (hM : X.Thc S.sK ka ≤ B.Mlat j ka)
    (hbe : be ≤ WeightFamilies.PPv D large₂ Ch Ah * ka.size) :
    ∃ th : Fin (WeightFamilies.rhoP B CRm T c j ka) → B.Mlat j ka,
      ({ G0 with rq := WeightFamilies.rhoP B CRm T c j ka, th := th } : GlobalFamilyData X ka wL wF).TiedQ large₂ S CRm T c Ch Ah := by
  obtain ⟨Sh, hSh, hspan, hshort⟩ := hS4
  have hMtop : Submodule.span B.KO (B.Mlat j ka : Set (B.Cusp j ka)) = ⊤ :=
    top_le_iff.mp (hspan ▸ Submodule.span_mono fun x hx => hM (hSh hx))
  have hex := exists_sub_basis Sh hspan (WeightFamilies.MggK B CRm T c j ka)
  rw [← rhoP_eq_finrank B CRm T c j ka hMtop] at hex
  obtain ⟨e, he, hsup⟩ := hex
  exact ⟨fun i => ⟨e i, hM (hSh (he i))⟩, rfl, fun i => hSh (he i), hsup, fun i => (hshort _ (he i)).trans hbe⟩

section Unchanged

variable {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} (G0 : GlobalFamilyData X ka wL wF) (rq : ℕ) (th : Fin rq → B.Mlat j ka)

variable {G0} {la : HeightOneSpectrum (𝓞 B.KO)} (Q : LocalPointData G0 la)

end Unchanged

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.SectionMonomialGenerators
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

section Base

variable (X : PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (N : ℕ) (ka : WeightFamilies.Wt D j)

theorem bcV_mem_Vw {x : X.Vl la} (hx : x ∈ T0.WL X ka la) : bcV X la N x ∈ Vw X la N ka := by
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, ⟨F', _, rfl⟩, rfl⟩ := hx
    exact emb_mem_Vw X la N ka F'
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add x y _ _ hx hy => rw [map_add (f := _)]; exact Submodule.add_mem _ hx hy
  | smul a x _ hx =>
    rw [map_smul, ← algebraMap_smul (Kp X la N) a]
    exact Submodule.smul_mem _ _ hx

def jW : ↥(T0.WL X ka la) →ₗ[X.Kl la] ↥(Vw X la N ka) :=
  ((bcV X la N).toLinearMap.domRestrict (T0.WL X ka la)).codRestrict ((Vw X la N ka).restrictScalars (X.Kl la))
    fun x => bcV_mem_Vw X la N ka x.2

def M1 : Submodule (Op X la N) ↥(Vw X la N ka) :=
  Submodule.span (Op X la N) (jW X la N ka '' (T0.MW X ka la : Set ↥(T0.WL X ka la)))

def Th1 (S : Scal B) (wL wF : WeightFamilies.Wt D j) (T : ℕ) : Submodule (Op X la N) ↥(Vw X la N ka) :=
  Submodule.span (Op X la N) (jW X la N ka '' (T0.ThW X S ka wL wF T la : Set ↥(T0.WL X ka la)))

def MggO (B : WeightFamilies.Prov D) (CRm T c : ℝ) (j : ℕ) (ka : WeightFamilies.Wt D j) : Submodule (𝓞 B.KO) (B.Cusp j ka) :=
  B.Mlat j ka ⊓ (WeightFamilies.MggK B CRm T c j ka).restrictScalars (𝓞 B.KO)

def MggW (CRm T c : ℝ) : Submodule (X.Ol la) ↥(T0.WL X ka la) :=
  T0.inW X ka la (X.loc la (X.emb ka (MggO B CRm T c j ka)))

def toW (F : B.Mlat j ka) : ↥(T0.WL X ka la) :=
  ⟨X.bc la (X.inc ka F), Submodule.subset_span ⟨X.inc ka F, ⟨F, F.2, rfl⟩, rfl⟩⟩

end Base

section Chain

variable {X : PJ D B P j} {wL wF : WeightFamilies.Wt D j} {T : ℕ} (G : GlobalFamilyData X (addL wF wL T) wL wF)
  (la : HeightOneSpectrum (𝓞 B.KO))

def sectionMonomialGenerators : Set ↥(Vw X la G.N (addL wF wL T)) :=
  {f | ∃ (al : Fin (WeightFamilies.dimY D j) → ℕ) (i : Fin G.del), ∑ i, al i < a0 D j T ∧
      (f : Rp X la G.N) = secPow X la G.w al * sec X la G.w 0 ^ (T - ∑ i, al i) * emb X la G.N (X.inc wF (G.th' i))}

def N1 : Submodule (Op X la G.N) ↥(Vw X la G.N (addL wF wL T)) := Submodule.span (Op X la G.N) (sectionMonomialGenerators G la)

def Zg : Set ↥(Vw X la G.N (addL wF wL T)) := {f | ∃ k : Fin G.rz, (f : Rp X la G.N) = zK G la k}

def Zl : Submodule (Op X la G.N) ↥(Vw X la G.N (addL wF wL T)) := Submodule.span (Op X la G.N) (Zg G la)

def ZK : Submodule (Kp X la G.N) ↥(Vw X la G.N (addL wF wL T)) := Submodule.span (Kp X la G.N) (Zg G la)

def NovK : Submodule (Kp X la G.N) ↥(Vw X la G.N (addL wF wL T)) :=
  Submodule.span (Kp X la G.N) ((N1 G la ⊔ Zl G la : Submodule (Op X la G.N) ↥(Vw X la G.N (addL wF wL T))) :
    Set ↥(Vw X la G.N (addL wF wL T)))

def Zm : Submodule (Op X la G.N) ↥(Vw X la G.N (addL wF wL T)) :=
  M1 X la G.N (addL wF wL T) ⊓ (ZK G la).restrictScalars (Op X la G.N)

def Np (e : ℕ) : Submodule (Op X la G.N) ↥(Vw X la G.N (addL wF wL T)) :=
  ((M1 X la G.N (addL wF wL T)).map ((unifO X la G.N ^ e) •
      (LinearMap.id : ↥(Vw X la G.N (addL wF wL T)) →ₗ[Op X la G.N] ↥(Vw X la G.N (addL wF wL T)))) ⊓
    (NovK G la).restrictScalars (Op X la G.N)) ⊔ N1 G la ⊔ Zm G la

def rhoO : ↥(Vw X la G.N (addL wF wL T)) →ₗ[Op X la G.N] WK X la G.w wF (a0 D j T) :=
  (rhoK X la G.w wF (a0 D j T) T).restrictScalars (Op X la G.N)

def rhoN (e : ℕ) : ↥(Np G la e) →ₗ[Op X la G.N] WK X la G.w wF (a0 D j T) :=
  rhoO G la ∘ₗ (Np G la e).subtype

theorem reducedGenerators_eq_map : firstLength_le_prime_bound G la T = (N1 G la).map (rhoO G la) := by
  unfold firstLength_le_prime_bound N1
  rw [Submodule.map_span]
  rfl

end Chain

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

-- bundled from Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.VEtNonnegOfTied
section
noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps

variable {D : D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

variable {X : PJ D B P j} {ka wL wF : WeightFamilies.Wt D j} {G : GlobalFamilyData X ka wL wF} {la : HeightOneSpectrum (𝓞 B.KO)}

def vEt (Q : LocalPointData G la) (ζ : PtsG G la) : ℝ :=
  if j < D.R.m then (X.vAt la (Q.y ζ) (X.inc _ G.et)).toReal / (2 * (G.iet : ℝ)) else 0

theorem ep_nu_int {S : Scal B} (Q : LocalPointData G la) (hTie : Q.InTie S) (ζ : PtsG G la) :
    ∃ n : ℤ, (ep (unifO X la G.N) ζ : ℝ) * Q.nu S ζ = n := (hTie ζ).2.2.2.1

theorem levels_eq [Fintype (PtsG G la)] (Q : LocalPointData G la) (T : ℕ) (c : ℝ) :
    (T : ℝ) * max 0 c * ∑ ζ, ((ep (unifO X la G.N) ζ : ℝ) * (fdeg ζ : ℝ)) * vEt Q ζ =
      if j < D.R.m then (T : ℝ) * (max 0 c / (2 * (G.iet : ℝ))) * Q.Net else 0 := by
  split_ifs with hj
  · unfold LocalPointData.Net vEt
    rw [finsum_eq_sum_of_fintype]
    simp only [if_pos hj]
    rw [Finset.mul_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun ζ _ => ?_
    ring
  · unfold vEt
    simp only [if_neg hj, mul_zero, Finset.sum_const_zero]

end Formalism.MainNotions.Gaps.EtaleWeightGaps
end
end

