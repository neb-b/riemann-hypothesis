module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SemisimpleLevels.CsdSsOfFull
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.ActUVariableEqPow
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.Bundle0004
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqEmbed
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.Bundle0034
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IwJqLine

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.LocData
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.PRep

open Polynomial in
private theorem trace_of_charpoly {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → ℂ)
    (h : M.charpoly = ∏ i, (X - C (c i))) : M.trace = ∑ i, c i := by
  have hr : M.charpoly.roots = Finset.univ.val.map c := by
    rw [h, Finset.prod_eq_multiset_prod, ← roots_multiset_prod_X_sub_C (Finset.univ.val.map c), Multiset.map_map]
    rfl
  rw [Matrix.trace_eq_sum_roots_charpoly, hr]
  rfl

open Polynomial in
private theorem rel_of_chars {W : Type} [Group W] {n q : ℕ} (hq : 2 ≤ q) (R : W →* GL (Fin n) ℂ) (c : Fin n → W →* ℂ)
    (h : ∀ g, (R g : Matrix (Fin n) (Fin n) ℂ).charpoly = ∏ i, (X - C (c i g))) (f t : W)
    (h1 : R ((t ^ q)⁻¹ * (f⁻¹ * t * f)) = 1) (h2 : ∀ i, c i ((t ^ q)⁻¹ * (f⁻¹ * t * f)) = 1)
    (h3 : ∀ i i', i ≠ i' → c i f ≠ c i' f ∧ c i f ≠ (q : ℂ) * c i' f) (i : Fin n) :
    (List.ofFn fun i' => if i' = i then 1 else (R f : Matrix (Fin n) (Fin n) ℂ) - c i' f • (1 : Matrix (Fin n) (Fin n) ℂ)).prod *
      ((R t : Matrix (Fin n) (Fin n) ℂ) - c i t • (1 : Matrix (Fin n) (Fin n) ℂ)) = 0 := by
  have hinv : ∀ i g, c i g⁻¹ * c i g = 1 := fun i g => by rw [← map_mul, inv_mul_cancel, map_one]
  have hne : ∀ i g, c i g ≠ 0 := fun i g h0 => by simpa [h0] using hinv i g
  have hR : R f⁻¹ * R t * (R f⁻¹)⁻¹ = R t ^ q := by
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    rw [← map_pow, h1]
    simp
  have hc : ∀ i, c i (t ^ (q - 1)) = 1 := fun i => by
    have e1 : c i (f⁻¹ * t * f) = c i t := by
      rw [map_mul, map_mul, mul_right_comm, hinv, one_mul]
    have e2 : c i (t ^ q) = c i t := by
      have := h2 i
      rw [map_mul, e1, ← hinv i (t ^ q)] at this
      exact (mul_left_cancel₀ (hne _ _) this).symm
    have e3 : t ^ q = t ^ (q - 1) * t := by rw [← pow_succ]; congr 1; omega
    rw [e3, map_mul] at e2
    exact mul_right_cancel₀ (hne i t) (e2.trans (one_mul _).symm)
  have hN : IsNilpotent (((R t ^ (q - 1) : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) - 1) := by
    refine ⟨n, ?_⟩
    have := Matrix.aeval_self_charpoly (R (t ^ (q - 1)) : Matrix (Fin n) (Fin n) ℂ)
    rw [h] at this
    simpa [hc] using this
  have ha : ∀ i j, c i f⁻¹ ≠ (q : ℂ) * c j f⁻¹ := fun i j e => by
    have e' : c j f = (q : ℂ) * c i f := by
      have a1 := hinv i f
      have a2 := hinv j f
      linear_combination (c j f * c i f) * e - c j f * a1 + q * c i f * a2
    by_cases hij : j = i
    · subst hij
      have : (1 : ℂ) = q := mul_right_cancel₀ (hne j f) ((one_mul _).trans e')
      have : 1 = q := by exact_mod_cast this
      omega
    · exact (h3 j i hij).2 e'
  have hcm := (tamePair ℂ n q (R f⁻¹) (R t) (fun i => c i f⁻¹) hq hR (h _) ha hN).2
  have hcm' : R f * R t = R t * R f := by
    rw [map_inv] at hcm
    exact (Commute.inv_left_iff.1 hcm : Commute (R f) (R t))
  refine pairRel ℂ n _ _ (fun i => c i f) (fun i => c i t) (fun i j e => ?_) ?_ (h f) (fun a => ?_) i
  · by_contra hij
    exact (h3 i j hij).1 e
  · rw [← Units.val_mul, hcm', Units.val_mul]
  · rw [← Units.val_pow_eq_pow_val, ← Units.val_mul, ← map_pow, ← map_mul, trace_of_charpoly _ _ (h _)]
    simp

private theorem chi_unit {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (ψ : Fin n → kˣ →* ℂˣ) (χ : (Fin n → kˣ) →* ℂˣ)
    (hχ : torusChar ψ = χ * ((deltaHalf k fun _ : Fin n => Unit).comp (leviTorus k (Fin n)).toMonoidHom))
    (i : Fin n) (u : kˣ) (hu : ord k u = 0) (h1 : ψ i u = 1) : χ (Pi.mulSingle i u) = 1 := by
  have e1 : torusChar ψ (Pi.mulSingle i u) = ψ i u := by
    rw [torusChar_apply, Finset.prod_eq_single i, Pi.mulSingle_eq_same]
    · intro j _ hj
      rw [Pi.mulSingle_eq_of_ne hj, map_one]
    · simp
  have hd : ∀ (t : Fin n → kˣ) j, Matrix.GeneralLinearGroup.det (leviTorus k (Fin n) t j) = t j := fun t =>
    congrFun ((leviTorus k (Fin n)).left_inv t)
  have e2 : deltaHalf k (fun _ : Fin n => Unit) (leviTorus k (Fin n) (Pi.mulSingle i u)) = 1 := by
    rw [deltaHalf_apply, Finset.prod_eq_single i, hd, Pi.mulSingle_eq_same]
    · refine Units.ext ?_
      rw [val_absPow, GlobalTheory.LGrp.nabs_eq_zpow, hu]
      simp
    · intro j _ hj
      rw [hd, Pi.mulSingle_eq_of_ne hj, map_one]
    · simp
  rw [hχ, h1, MonoidHom.mul_apply, MonoidHom.comp_apply] at e1
  erw [e2] at e1
  simpa using e1

theorem UpperTheory.V.Pa.Lev.locData :
    LocP → ∀ (l : ℕ) [Fact l.Prime] (E Ω : Type) [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] (Bq : ValuationSubring Ω) (w : HeightOneSpectrum (𝓞 E)) (hB : IsPlaceOver Bq w), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ fr τ : G E Ω, fr ∈ Dec (F := E) Bq → IsFrob (F := E) Bq (normV w) fr⁻¹ → GlobalTheory.TameQuot.IsProGen E Bq l τ → resCard (w.adicCompletion E) = normV w ∧ ∃ x δ : (w.adicCompletion E)ˣ, IsUnif x ∧ IsGenMod _ (ellC l _) δ ∧ ∀ (n : ℕ) (ι : Qbar l ≃+* ℂ) (r : G E Ω →* GL (Fin n) (Qbar l)) (σ : SmIrr (GL (Fin n) (w.adicCompletion E))), (∀ rc : IrrGL (k := w.adicCompletion E) → WD hB, IsRec hB rc → UpperTheory.V.Lev.WO ι r (rc (algNorm σ))) → LocRel l x δ σ.ρ ((r fr : Matrix (Fin n) (Fin n) (Qbar l)).map ι) ((r τ : Matrix (Fin n) (Fin n) (Qbar l)).map ι) := by
  intro hP l _ E Ω _ _ _ _ _ Bq w hB hl fr τ hfr hF hτ
  obtain ⟨rc, hrc, -⟩ := hP.ll.1 E Ω Bq w hB
  obtain ⟨a, ha, ε, -, L⟩ := id hrc
  obtain ⟨hq, h1, h2, hx, hδ, hk, hrel⟩ := artinEl hP.tame l E Ω Bq w hB hl a ha fr τ hfr hF hτ
  refine ⟨hq, _, _, hx, hδ, fun n ι r σ H C hC θ hθ χ hχ α hα => ?_⟩
  obtain ⟨ψ, hψ, hψC, hψχ, hsub⟩ := jqEmbed hP.bz _ n C σ.V σ.ρ σ.smooth σ.irred θ hθ χ hχ
  have hν := nuChar l E Ω Bq w hB hl a ha ε rc L n σ ψ χ hψ hψχ hsub
  obtain ⟨hw1, hw2⟩ := wdChar l E Ω Bq w hB hl n ι r _ (H rc hrc)
  have hq2 : 2 ≤ resCard (w.adicCompletion E) := Finite.one_lt_card (α := 𝓀[w.adicCompletion E])
  have hq0 : (resCard (w.adicCompletion E) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  let c : Fin n → Weil hB →* ℂ := fun i =>
    { toFun := fun g => (resCard (w.adicCompletion E) : ℂ) ^ (((i : ℕ) : ℤ) * ord (w.adicCompletion E) (a g)) *
        (χ (Pi.mulSingle i (a g)) : ℂ)
      map_one' := by
        rw [map_one, Pi.mulSingle_one, map_one, ord_eq_zero (by simp)]
        simp
      map_mul' := fun g g' => by
        rw [map_mul, ord_mul, Pi.mulSingle_mul, map_mul, mul_add, zpow_add₀ hq0, Units.val_mul]
        ring }
  let R : Weil hB →* GL (Fin n) ℂ :=
    ((Matrix.GeneralLinearGroup.map ι.toRingHom).comp r).comp (Weil hB).subtype
  have hR : ∀ g, (R g : Matrix (Fin n) (Fin n) ℂ).charpoly = ∏ i, (Polynomial.X - Polynomial.C (c i g)) :=
    fun g => (hw1 g).trans (hν g)
  have hord : ∀ g : Weil hB, (g : G E Ω) ∈ Ine (F := E) Bq → ord (w.adicCompletion E) (a g) = 0 := fun g hg => by
    rw [ha.ord_eq, deg_eq_zero_iff.2 hg, neg_zero]
  have hf : ∀ i, α i = c i ⟨fr, h1⟩ := fun i => by
    have e : ord (w.adicCompletion E) (a ⟨fr, h1⟩) = 1 := by
      have h2 : deg (⟨fr, h1⟩ : Weil hB)⁻¹ = 1 := deg_eq_one_iff.2 hF
      rw [ha.ord_eq, ← deg_inv, h2]
    rw [hα]
    change _ = (resCard (w.adicCompletion E) : ℂ) ^ (((i : ℕ) : ℤ) * ord (w.adicCompletion E) (a ⟨fr, h1⟩)) * _
    rw [e, mul_one, zpow_natCast]
  have ht : ∀ i, (χ (Pi.mulSingle i (a ⟨τ, h2⟩)) : ℂ) = c i ⟨τ, h2⟩ := fun i => by
    change _ = (resCard (w.adicCompletion E) : ℂ) ^ (((i : ℕ) : ℤ) * ord (w.adicCompletion E) (a ⟨τ, h2⟩)) * _
    rw [hord _ hτ.1, mul_zero, zpow_zero, one_mul]
  obtain rfl : α = fun i => c i ⟨fr, h1⟩ := funext hf
  refine ⟨hR ⟨fr, h1⟩, fun hgen i => ?_⟩
  rw [ht]
  set g : Weil hB := ((⟨τ, h2⟩ : Weil hB) ^ resCard (w.adicCompletion E))⁻¹ *
    ((⟨fr, h1⟩ : Weil hB)⁻¹ * ⟨τ, h2⟩ * ⟨fr, h1⟩) with hg
  have hgk : (g : G E Ω) ∈ GlobalTheory.TameQuot.ineKer E Bq l := by
    rw [← hq] at hrel
    exact hrel
  have hcg : ∀ i, c i g = 1 := fun i => by
    have e := hord g (GlobalTheory.TameQuot.ineKer_le_Ine Bq l hgk)
    have e2 : a g ∈ unitsC _ C := Subgroup.map_mono (Subgroup.comap_mono hC) (hk g g.2 hgk)
    change (resCard (w.adicCompletion E) : ℂ) ^ (((i : ℕ) : ℤ) * ord (w.adicCompletion E) (a g)) *
      (χ (Pi.mulSingle i (a g)) : ℂ) = 1
    rw [e, chi_unit ψ χ hψχ i _ e (hψC i _ e2)]
    simp
  have hRg : R g = 1 := by
    have e : r g = 1 := hw2 g hgk (((hw1 g).trans (hν g)).trans (by
      change ∏ i, (Polynomial.X - Polynomial.C (c i g)) = _
      simp [hcg]))
    change Matrix.GeneralLinearGroup.map ι.toRingHom (r g) = 1
    rw [e, map_one]
  exact rel_of_chars hq2 R c hR ⟨fr, h1⟩ ⟨τ, h2⟩ hRg hcg hgen i
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.NilpotentLevelLowering.NilKill
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N ValuativeRel IsLocalRing
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil
open UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Pa UpperTheory.V.Pa.Lev
open scoped TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem nilKill_split {k : Type} [Field k] [ValuativeRel k] {n : ℕ} (t : Fin n → kˣ) :
    ∃ c : kˣ, ∀ s : Fin n → kˣ, (s = 1 ∨ s = t) → ∀ i j : Fin n, i ≤ j →
      valuation k ((s i * c ^ (n - i) : kˣ) : k) ≤ valuation k ((s j * c ^ (n - j) : kˣ) : k) := by
  rcases isEmpty_or_nonempty (Fin n) with h | h
  · exact ⟨1, fun _ _ i => h.elim i⟩
  obtain ⟨p, hp⟩ := Finite.exists_min (fun p : Fin n × Fin n => valuation k ((t p.2 * (t p.1)⁻¹ : kˣ) : k))
  set c : kˣ := t p.2 * (t p.1)⁻¹ with hc
  have h1 : valuation k (c : k) ≤ 1 := by simpa using hp (p.1, p.1)
  refine ⟨c, fun s hs i j hij => ?_⟩
  rcases hij.eq_or_lt with rfl | hlt
  · exact le_rfl
  have h2 : valuation k (s i : k) * valuation k (c : k) ≤ valuation k (s j : k) := by
    rcases hs with rfl | rfl
    · simpa using h1
    · have := mul_le_mul_right (hp (i, j)) (valuation k (s i : k))
      refine this.trans (le_of_eq ?_)
      rw [← map_mul, ← Units.val_mul]
      congr 2
      simp
  have hj := j.2
  have hlt' : (i : ℕ) < j := hlt
  have e : n - (i : ℕ) = 1 + ((n - j) + (j - i - 1)) := by omega
  rw [e]
  simp only [Units.val_mul, Units.val_pow_eq_pow_val, map_mul, map_pow, pow_add, pow_one]
  rw [← mul_assoc]
  exact mul_le_mul' h2 (mul_le_of_le_one_right' (pow_le_one' h1 _))

private theorem nilKill_dc {A M A' M' G : Type} [CommRing A] [AddCommGroup M] [Module A M] [CommRing A'] [AddCommGroup M']
    [Module A' M'] [Group G] (ρ : Representation A G M) (ρ' : Representation A' G M') (K K' : Subgroup G) (x : G)
    (hx : FinOrb K K' x) (f : M →+ M') (hf : ∀ g m, f (ρ g m) = ρ' g (f m)) (m : M) :
    dc ρ' K K' x (f m) = f (dc ρ K K' x m) := by
  haveI : Fintype (MulAction.orbit K (x : G ⧸ K')) := Set.Finite.fintype hx
  unfold dc
  set_option synthInstance.maxHeartbeats 100000 in
    rw [finsum_eq_sum_of_fintype, finsum_eq_sum_of_fintype, LinearMap.sum_apply, LinearMap.sum_apply, map_sum]
  exact Finset.sum_congr rfl fun q _ => (hf _ _).symm

private theorem nilKill_ext {A N A' N' T : Type} [CommRing A] [AddCommGroup N] [Module A N] [CommRing A'] [AddCommGroup N']
    [Module A' N'] [Group T] (θ : T →* (Module.End A N)ˣ) (θ' : T →* (Module.End A' N')ˣ) (g : N → N') (t b : T)
    (hb : ∀ m, (θ' b).val (g m) = g ((θ b).val m)) (ha : ∀ m, (θ' (b * t)).val (g m) = g ((θ (b * t)).val m)) (m : N) :
    (θ' t).val (g m) = g ((θ t).val m) := by
  have hinj : Function.Injective (θ' b).val := ((Module.End.isUnit_iff _).1 (θ' b).isUnit).1
  apply hinj
  have h := ha m
  rw [map_mul, map_mul, Units.val_mul, Units.val_mul, Module.End.mul_apply, Module.End.mul_apply] at h
  rw [h, hb]

private theorem nilKill_eig {T W : Type} [CommGroup T] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (θ : T →* (Module.End ℂ W)ˣ) (S0 : Submodule ℂ W) (h0 : S0 ≠ ⊥)
    (h1 : ∀ t, ∀ v ∈ S0, (θ t : Module.End ℂ W) v ∈ S0) :
    ∃ χ : T →* ℂˣ, ∃ v ∈ S0, v ≠ 0 ∧ ∀ t, (θ t : Module.End ℂ W) v = (χ t : ℂ) • v := by
  obtain ⟨S, ⟨hS0, hle, hS⟩, hmin⟩ := (wellFounded_lt (α := Submodule ℂ W)).has_min
    {S | S ≠ ⊥ ∧ S ≤ S0 ∧ ∀ t, ∀ v ∈ S, (θ t : Module.End ℂ W) v ∈ S} ⟨S0, h0, le_rfl, h1⟩
  have : Nontrivial S := Submodule.nontrivial_iff_ne_bot.2 hS0
  have key : ∀ t, ∃ c : ℂ, ∀ v ∈ S, (θ t : Module.End ℂ W) v = c • v := fun t => by
    obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue ((θ t : Module.End ℂ W).restrict (hS t))
    obtain ⟨w, hw⟩ := hc.exists_hasEigenvector
    have hw1 : (θ t : Module.End ℂ W) w = c • (w : W) := congrArg Subtype.val hw.apply_eq_smul
    refine ⟨c, fun v hv => ?_⟩
    have h1 : S ⊓ Module.End.eigenspace (θ t : Module.End ℂ W) c = S := by
      by_contra hne
      refine hmin _ ⟨?_, inf_le_left.trans hle, ?_⟩ (lt_of_le_of_ne inf_le_left hne)
      · exact (Submodule.ne_bot_iff _).2 ⟨w, ⟨w.2, Module.End.mem_eigenspace_iff.2 hw1⟩,
          fun h => hw.2 (Subtype.ext h)⟩
      · rintro s x ⟨hx, hx'⟩
        refine ⟨hS s x hx, Module.End.mem_eigenspace_iff.2 ?_⟩
        rw [← Module.End.mul_apply, ← Units.val_mul, ← map_mul, mul_comm, map_mul, Units.val_mul,
          Module.End.mul_apply, Module.End.mem_eigenspace_iff.1 hx', map_smul]
    rw [← h1] at hv
    exact Module.End.mem_eigenspace_iff.1 hv.2
  choose c hc using key
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hS0
  let c' : T →* ℂ :=
    { toFun := c
      map_one' := by
        have := hc 1 v hv
        rw [map_one, Units.val_one, Module.End.one_apply] at this
        exact smul_left_injective ℂ hv0 (this.symm.trans (one_smul _ _).symm)
      map_mul' := fun s t => by
        have := hc (s * t) v hv
        rw [map_mul, Units.val_mul, Module.End.mul_apply, hc t v hv, map_smul, hc s v hv, smul_smul,
          mul_comm] at this
        exact smul_left_injective ℂ hv0 this.symm }
  refine ⟨c'.toHomUnits, v, hle hv, hv0, fun t => ?_⟩
  rw [hc t v hv]
  simp [c']

private theorem nilKill_act {T W κ : Type} [CommGroup T] [AddCommGroup W] [Module ℂ W]
    (θ : T →* (Module.End ℂ W)ˣ) (t : κ → T) :
    ∃ act : MvPolynomial κ ℂ →ₐ[ℂ] Module.End ℂ W, ∀ a, act (MvPolynomial.X a) = θ (t a) :=
  ⟨(MonoidAlgebra.lift ℂ (Module.End ℂ W) T ((Units.coeHom _).comp θ)).comp
    (MvPolynomial.aeval fun a => MonoidAlgebra.single (t a) 1), fun a => by simp⟩

private theorem nilKill_int {W W' κ : Type} [AddCommGroup W] [Module ℂ W] [AddCommGroup W'] [Module ℂ W']
    (act : MvPolynomial κ ℂ →ₐ[ℂ] Module.End ℂ W) (act' : MvPolynomial κ ℂ →ₐ[ℂ] Module.End ℂ W') (g : W →ₗ[ℂ] W')
    (h : ∀ a v, act' (MvPolynomial.X a) (g v) = g (act (MvPolynomial.X a) v)) (F : MvPolynomial κ ℂ) (v : W) :
    act' F (g v) = g (act F v) := by
  induction F using MvPolynomial.induction_on generalizing v with
  | C c =>
    rw [← MvPolynomial.algebraMap_eq, AlgHom.commutes, AlgHom.commutes]
    simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p a hp => simp [h, hp]

private theorem nilKill_nil {T W κ : Type} [CommGroup T] [AddCommGroup W] [Module ℂ W] [FiniteDimensional ℂ W]
    (θ : T →* (Module.End ℂ W)ˣ) (t : κ → T) (act : MvPolynomial κ ℂ →ₐ[ℂ] Module.End ℂ W)
    (hact : ∀ a, act (MvPolynomial.X a) = θ (t a)) (F : MvPolynomial κ ℂ)
    (hF : ∀ χ : T →* ℂˣ, (⨅ s, Module.End.maxGenEigenspace (θ s : Module.End ℂ W) (χ s : ℂ)) ≠ ⊥ →
      MvPolynomial.eval (fun a => (χ (t a) : ℂ)) F = 0) (N : ℕ) (hN : Module.finrank ℂ W ≤ N) :
    act (F ^ N) = 0 := by
  by_contra hne
  have h0 : LinearMap.range (act (F ^ N)) ≠ ⊥ := fun h => hne (LinearMap.range_eq_bot.1 h)
  obtain ⟨χ, v, ⟨u, rfl⟩, hv0, hv⟩ := nilKill_eig θ _ h0 (by
    rintro s _ ⟨u, rfl⟩
    refine ⟨(θ s : Module.End ℂ W) u, nilKill_int act act _ (fun a v => ?_) _ _⟩
    rw [hact, ← Module.End.mul_apply, ← Module.End.mul_apply, ← Units.val_mul, ← Units.val_mul, ← map_mul,
      ← map_mul, mul_comm])
  have hχ := hF χ ((Submodule.ne_bot_iff _).2 ⟨_, (Submodule.mem_iInf _).2 fun s =>
    (Module.End.mem_maxGenEigenspace _ _ _).2 ⟨1, by rw [pow_one, LinearMap.sub_apply, hv s]; simp⟩, hv0⟩)
  have hev : ∀ G : MvPolynomial κ ℂ, act G (act (F ^ N) u) =
      MvPolynomial.eval (fun a => (χ (t a) : ℂ)) G • act (F ^ N) u := by
    intro G
    generalize act (F ^ N) u = x at hv
    induction G using MvPolynomial.induction_on with
    | C c =>
      rw [MvPolynomial.eval_C, ← MvPolynomial.algebraMap_eq, AlgHom.commutes]
      simp
    | add p q hp hq => simp [hp, hq, add_smul]
    | mul_X p a hp =>
      rw [map_mul, map_mul, Module.End.mul_apply, hact, hv, map_smul, hp, MvPolynomial.eval_X, smul_smul, mul_comm]
  have h1 : u ∈ LinearMap.ker (act F ^ (N + 1)) := by
    rw [LinearMap.mem_ker, pow_succ', Module.End.mul_apply, ← map_pow, hev, hχ, zero_smul]
  have h2 := Module.End.ker_pow_le_ker_pow_finrank _ _ h1
  apply hv0
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le' hN
  rw [map_pow, pow_add, Module.End.mul_apply, LinearMap.mem_ker.1 h2, map_zero]

private theorem nilKill_loc (hG : GlobalTheory.Published.GeometricLemma) (hBZ : GlobalTheory.Published.BernsteinZelevinskyFiniteness)
    {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
    (C : Subgroup 𝓀[k]ˣ) {Y : Type} [AddCommGroup Y] [Module ℂ Y] (π : Representation ℂ (GL (Fin n) k) Y)
    (σ : SmIrr (GL (Fin n) k)) (hs : IsoSum π ⊤ σ) {κ : Type} (t : κ → Fin n → kˣ) (θY) (hY : IsTheta π C θY)
    (act : MvPolynomial κ ℂ →ₐ[ℂ] Module.End ℂ (fixd π (iwC k n C))) (hact : ∀ a, act (MvPolynomial.X a) = θY (t a))
    (F : MvPolynomial κ ℂ) (hF : ∀ θ, IsTheta σ.ρ C θ → ∀ χ : (Fin n → kˣ) →* ℂˣ,
      (⨅ t, Module.End.maxGenEigenspace (θ t : Module.End ℂ (fixd σ.ρ (iwC k n C))) (χ t : ℂ)) ≠ ⊥ →
      MvPolynomial.eval (fun a => (χ (t a) : ℂ)) F = 0) : act (F ^ n.factorial) = 0 := by
  have hq : IsUnit (resCard k : ℂ) := (Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[k])).ne').isUnit
  obtain ⟨θ, hθ, -⟩ := thetaEx k n C ℂ σ.V σ.ρ hq
  obtain ⟨hfd, hrk, -⟩ := jqLine hG hBZ k n C σ.V σ.ρ σ.smooth σ.irred
  obtain ⟨actσ, hσ⟩ := nilKill_act θ t
  have hnil := nilKill_nil θ t actσ hσ F (hF θ hθ) _ hrk
  have ho : IsOpen (iwC k n C : Set (GL (Fin n) k)) :=
    Subgroup.isOpen_mono (H₁ := KOne k (Fin n)) (le_sup_left.trans le_sup_left) GlobalTheory.StepData.isOpen_KOne
  have hle : iwC k n C ≤ iwahori k (Fin n) := fun g hg => (((memIwC k n C).1 g).1 hg).1
  have hc : IsCompact (iwC k n C : Set (GL (Fin n) k)) :=
    (IwahoriOnto.isCompact_iwahori k (Fin n)).of_isClosed_subset (Subgroup.isClosed_of_isOpen _ ho) hle
  refine LinearMap.ext fun y => ?_
  have hy := isoFix k n Y π σ _ hc hs y y.2
  have hsub : (⨆ f : {f : σ.V →ₗ[ℂ] Y // ∀ g v, f (σ.ρ g v) = π g (f v)}, (fixd σ.ρ (iwC k n C)).map f.1) ≤
      (LinearMap.ker (act (F ^ n.factorial))).map (fixd π (iwC k n C)).subtype := by
    refine iSup_le ?_
    rintro ⟨f, hf⟩ _ ⟨v, hv, rfl⟩
    let g : fixd σ.ρ (iwC k n C) →ₗ[ℂ] fixd π (iwC k n C) :=
      f.restrict fun x hx u hu => by rw [← hf, hx u hu]
    have hd : ∀ s, Dom s → ∀ v, (θY s).val (g v) = g ((θ s).val v) := by
      intro s hs v
      apply Subtype.ext
      change _ = f _
      have hfin : FinOrb (iwC k n C) (iwC k n C) (diagT k (Fin n) s) := (heckePairIwC _ n C).1 _
      rw [hY s hs, hθ s hs]
      refine ((hkApply ℂ _ Y π _ _ _ hfin).1 (g v)).trans ?_
      refine (nilKill_dc σ.ρ π _ _ _ hfin f.toAddMonoidHom hf v).trans ?_
      exact congrArg f ((hkApply ℂ _ σ.V σ.ρ _ _ _ hfin).1 v).symm
    have hall : ∀ s v, (θY s).val (g v) = g ((θ s).val v) := by
      intro s v
      obtain ⟨c, hc⟩ := nilKill_split s
      refine nilKill_ext θ θY g s (fun i : Fin n => c ^ (n - (i : ℕ))) (hd _ ?_) (hd _ ?_) v
      · intro i i' hi
        simpa using hc 1 (Or.inl rfl) i i' hi
      · rw [mul_comm]
        exact hc s (Or.inr rfl)
    refine ⟨g ⟨v, hv⟩, ?_, rfl⟩
    change act _ _ = 0
    rw [nilKill_int actσ act g (fun a v => by rw [hact, hσ, hall]), hnil, LinearMap.zero_apply, map_zero]
  obtain ⟨y', hy', e⟩ := hsub hy
  obtain rfl : y' = y := Subtype.ext e
  exact hy'

theorem UpperTheory.V.Pa.Lev.nilKill :
    GlobalTheory.Published.GeometricLemma → GlobalTheory.Published.BernsteinZelevinskyFiniteness → ∀ (L : Type) [Field L] [NumberField L] (n q : ℕ) (w : Fin q → Plc L) (Y : Type) [AddCommGroup Y] [Module ℂ Y] (π : Representation ℂ (GV n w) Y) (C : ∀ j, Subgroup 𝓀[(w j).adicCompletion L]ˣ) (Θ), IsThetaQ π C Θ → ∀ (j : Fin q) (σ : SmIrr (GLw n (w j))), IsoSum (π.comp (atJ n w j)) ⊤ σ → ∀ (κ : Type) (t : κ → Fin n → ((w j).adicCompletion L)ˣ) (act : MvPolynomial κ ℂ →ₐ[ℂ] Module.End ℂ (fixd π (UC n w C))), (∀ a, act (MvPolynomial.X a) = Θ j (t a)) → ∀ F : MvPolynomial κ ℂ, (∀ θ, IsTheta σ.ρ (C j) θ → ∀ χ : (Fin n → ((w j).adicCompletion L)ˣ) →* ℂˣ, (⨅ t, Module.End.maxGenEigenspace (θ t : Module.End ℂ (fixd σ.ρ (iwC _ n (C j)))) (χ t : ℂ)) ≠ ⊥ → MvPolynomial.eval (fun a => (χ (t a) : ℂ)) F = 0) → act (F ^ n.factorial) = 0 := by
  intro hG hBZ L _ _ n q w Y _ _ π C Θ hΘ j σ hs κ t act hact F hF
  have hq : IsUnit (resCard ((w j).adicCompletion L) : ℂ) :=
    (Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[(w j).adicCompletion L])).ne').isUnit
  obtain ⟨θY, hY, -⟩ := thetaEx _ n (C j) ℂ Y (π.comp (atJ n w j)) hq
  obtain ⟨actY, haY⟩ := nilKill_act θY t
  have h0 := nilKill_loc hG hBZ (C j) (π.comp (atJ n w j)) σ hs t θY hY actY haY F hF
  have hle : fixd π (UC n w C) ≤ fixd (π.comp (atJ n w j)) (iwC _ n (C j)) := by
    intro x hx u hu
    refine hx (atJ n w j u) fun j' _ => ?_
    by_cases h : j' = j
    · subst h
      simpa [atJ] using hu
    · have : atJ n w j u j' = 1 := Pi.mulSingle_eq_of_ne (M := fun j => GLw n (w j)) h u
      rw [this]
      exact (iwC _ n (C j')).one_mem
  refine LinearMap.ext fun m => Submodule.inclusion_injective hle ?_
  rw [← nilKill_int act actY (Submodule.inclusion hle) (fun a v => ?_), h0, LinearMap.zero_apply,
    LinearMap.zero_apply, map_zero]
  rw [haY, hact]
  exact Subtype.ext (thetaLoc L n q w ℂ Y π C Θ hΘ j θY hY (t a) v _ rfl)
end

