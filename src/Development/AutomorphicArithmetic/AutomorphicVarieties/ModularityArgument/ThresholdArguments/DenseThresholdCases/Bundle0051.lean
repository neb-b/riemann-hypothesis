module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.DiscreteSeriesCoefficientsCuspidal
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0044
public import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.OrdinaryHeckeCharacters.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.OrdA
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.WeilDeligneUnramified.WeilCharpolySupport.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.Bundle0040

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCoreEig
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem eig_cont {Γ R K : Type} [TopologicalSpace Γ] [CommRing R] [NormedField K] (I : Ideal R) (y : R →+* K) (a : ℝ)
    (h1 : a < 1) (h0 : 0 ≤ a) (hy : ∀ N, ∀ x ∈ I ^ N, ‖y x‖ ≤ a ^ N) {f : Γ → R} (hf : Alg.AdicCont I f) :
    Continuous fun g => y (f g) := by
  refine continuous_iff_continuousAt.2 fun g => Metric.tendsto_nhds.2 fun ε hε => ?_
  obtain ⟨N, hN⟩ := ((tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).eventually (gt_mem_nhds hε)).exists
  filter_upwards [(hf N).eventually_eq g] with g' hg'
  rw [dist_eq_norm, ← map_sub]
  exact (hy N _ (Ideal.Quotient.eq.1 hg')).trans_lt hN
private theorem eig_chi_map {n : ℕ} {A B G : Type} [CommRing A] [CommRing B] [Group G] (D : W.GDet n A G) (f : A →+* B)
    (g : G) : (D.map f).chi (MonoidAlgebra.single g 1) = (D.chi (MonoidAlgebra.single g 1)).map f := by
  letI : Algebra A (Polynomial B) := ((algebraMap B (Polynomial B)).comp f).toAlgebra
  let φ : Polynomial A →ₐ[A] Polynomial B :=
    { Polynomial.mapRingHom f with commutes' := fun a => Polynomial.map_C f }
  have h := D.nat (Polynomial A) (Polynomial B) φ
    (MonoidAlgebra.single 1 Polynomial.X - MonoidAlgebra.mapRingHom G Polynomial.C (MonoidAlgebra.single g 1))
  refine Eq.trans ?_ h
  change D.D (Polynomial B) _ = D.D (Polynomial B) (MonoidAlgebra.mapRingHom G (Polynomial.mapRingHom f) _)
  congr 1
  simp [map_sub, MonoidAlgebra.mapRingHom_single]
private theorem eig_pol {A B : Type} [CommRing A] [CommRing B] (f : A →+* B) (n q : ℕ) (a : ℕ → A) (b : ℕ → B)
    (h : ∀ j ≤ n, f (a j) = b j) : (Hi.heckePol n q a).map f = Hi.heckePol n q b := by
  unfold Hi.heckePol
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Polynomial.map_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [Polynomial.map_mul, Polynomial.map_pow, map_X, map_C, map_mul, h j (Nat.lt_succ_iff.1 (Finset.mem_range.1 hj))]
  simp
private theorem eig_tele {n : ℕ} {K : Type} [Field K] (f g : Fin n → K) (hg : ∀ i, g i ≠ 0)
    (h : ∀ j, ∏ i with i ≤ j, f i = ∏ i with i ≤ j, g i) (j : Fin n) : f j = g j := by
  induction j using WellFoundedLT.induction with
  | ind j ih =>
    have e : Finset.univ.filter (fun i => i ≤ j) = insert j (Finset.univ.filter fun i => i < j) := by
      ext i; simp [le_iff_eq_or_lt]
    have h1 := h j
    rw [e, Finset.prod_insert (by simp), Finset.prod_insert (by simp),
      Finset.prod_congr rfl fun i hi => ih i (by simpa using hi)] at h1
    exact mul_right_cancel₀ (Finset.prod_ne_zero_iff.2 fun i _ => hg i) h1
private theorem eig_gen {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {S K : Type} [Group S] [Field K] (a : S →* kˣ) (ha : Function.Surjective a) (P Q : S →* K)
    (h1 : ∀ s, a s ∈ Uo k → P s = Q s) (h2 : ∀ s, a s = unif k → P s = Q s) (s : S) : P s = Q s := by
  obtain ⟨t, ht⟩ := ha (unif k)
  have e : s = s * (t ^ ord k (a s))⁻¹ * t ^ ord k (a s) := by group
  have h3 : a (s * (t ^ ord k (a s))⁻¹) ∈ Uo k := by
    rw [map_mul, map_inv, map_zpow, ht, ← div_eq_mul_inv]
    exact GlAx.val_div_ord _
  rw [e, map_mul, map_mul Q, h1 _ h3, map_zpow, map_zpow, h2 t ht]
section Pow
variable {F : Type} [Field F] [NumberField F] {l : ℕ} [Fact l.Prime] (w : HeightOneSpectrum (𝓞 F))
private theorem eig_ne (hh : (F →+* Qbar l) → ℤ) (x : (w.adicCompletion F)ˣ) : algPow w hh (x : w.adicCompletion F) ≠ 0 := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite {j : w.adicCompletion F →+* Qbar l // Continuous j}
  unfold algPow
  rw [finprod_eq_prod_of_fintype]
  exact Finset.prod_ne_zero_iff.2 fun j _ => zpow_ne_zero _ ((map_ne_zero j.1).2 x.ne_zero)
private theorem eig_mul (hh : (F →+* Qbar l) → ℤ) (x y : w.adicCompletion F) :
    algPow w hh (x * y) = algPow w hh x * algPow w hh y := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  unfold algPow
  rw [← finprod_mul_distrib (Set.toFinite _) (Set.toFinite _)]
  exact finprod_congr fun j => by rw [map_mul, mul_zpow]
private theorem eig_ht {n : ℕ} (lam : Wt F l n) (i : Fin n) (x : (w.adicCompletion F)ˣ) :
    algPow w (-htW lam i) (x : w.adicCompletion F) * algPow w (lowW lam i) (x : w.adicCompletion F) *
      algPow w (fun _ => 1) (x : w.adicCompletion F) ^ (i : ℕ) = 1 := by
  haveI := GlobalTheory.HeckeGal.finite_contEmb (l := l) w
  haveI := Fintype.ofFinite {j : w.adicCompletion F →+* Qbar l // Continuous j}
  unfold algPow
  simp only [finprod_eq_prod_of_fintype]
  rw [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
  refine Finset.prod_eq_one fun j _ => ?_
  have h0 : j.1 (x : w.adicCompletion F) ≠ 0 := (map_ne_zero j.1).2 x.ne_zero
  rw [zpow_one, ← zpow_natCast, ← zpow_add₀ h0, ← zpow_add₀ h0]
  simp [htW]
end Pow
private theorem eig_loc (hG : GlobalTheory.Published.GlobalArtinReciprocity) {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver B w)
    (hl : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) (a : Weil h →* (w.adicCompletion F)ˣ) (ha : IsLocalArtin h a) (ι : Qbar l ≃+* ℂ)
    (lam : Wt F l n) (ω : Fin n → (w.adicCompletion F)ˣ →* ℂˣ) (ψ : Fin n → Weil h →* Qbar l)
    (h1 : ∀ i s, a s ∈ Uo _ → ψ i s * (cycBar F Ω l (s : G F Ω) : Qbar l) ^ (i : ℕ) *
      algPow w (lowW lam i) (a s : w.adicCompletion F) = ι.symm (ω i (a s)))
    (h2 : ∀ (j : Fin n) s, a s = Hi.unif _ → ι (∏ i with i ≤ j, ψ i s * (cycBar F Ω l (s : G F Ω) : Qbar l) ^ (i : ℕ)) =
      (ι (∏ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < j + 1,
        algPow w (lowW lam i) ((Hi.unif (w.adicCompletion F) : (w.adicCompletion F)ˣ) : w.adicCompletion F)))⁻¹ * psEig ω (j + 1))
    (i : Fin n) (s : Weil h) : ψ i s = ι.symm (ω i (a s)) * algPow w (-htW lam i) (a s : w.adicCompletion F) := by
  let Q : Weil h →* Qbar l :=
    { toFun := fun s => ι.symm (ω i (a s)) * algPow w (-htW lam i) (a s : w.adicCompletion F)
      map_one' := by simp [algPow]
      map_mul' := fun s t => by
        simp only [map_mul, Units.val_mul, eig_mul]
        ring }
  have he := Loc.epsArt hG h hl a ha
  have hq : ((normV w : ℕ) : Qbar l) ≠ 0 := by
    rw [← resCard_eq_normV]
    exact Nat.cast_ne_zero.2 (Nat.card_pos (α := 𝓀[w.adicCompletion F])).ne'
  refine eig_gen a ha.surj (ψ i) Q (fun s hs => ?_) (fun s hs => ?_) s
  · have hd : deg s = 0 := by
      have := ha.ord_eq s
      rw [ord_eq_zero hs] at this
      omega
    have e1 := h1 i s hs
    rw [he, hd, zpow_zero, one_mul] at e1
    have e2 := eig_ht w lam i (a s)
    change _ = ι.symm (ω i (a s)) * algPow w (-htW lam i) (a s : w.adicCompletion F)
    rw [← e1]
    linear_combination (-ψ i s) * e2
  · have hd : deg s = -1 := by
      have := ha.ord_eq s
      rw [hs, ord_eq_one GlAx.unif_spec] at this
      omega
    have e1 := eig_tele (fun i => ψ i s * (cycBar F Ω l (s : G F Ω) : Qbar l) ^ (i : ℕ))
      (fun i => (algPow w (lowW lam i) (a s : w.adicCompletion F))⁻¹ * (ι.symm (ω i (a s)) * (((normV w : ℕ) : Qbar l) ^ (i : ℕ))⁻¹))
      (fun i => mul_ne_zero (inv_ne_zero (eig_ne w _ _)) (mul_ne_zero ((map_ne_zero ι.symm).2 (Units.ne_zero _))
        (inv_ne_zero (pow_ne_zero _ hq)))) (fun j => ι.injective ?_) i
    · have e2 := eig_ht w lam i (a s)
      have e3 := eig_ne w (lowW lam i) (a s)
      have e4 := pow_ne_zero (i : ℕ) hq
      rw [he, hd, mul_pow, zpow_neg_one, inv_pow] at e1
      change _ = ι.symm (ω i (a s)) * algPow w (-htW lam i) (a s : w.adicCompletion F)
      field_simp at e1
      linear_combination (-ψ i s) * e2 + algPow w (-htW lam i) (a s : w.adicCompletion F) * e1
    · have e : (Finset.univ.filter fun i : Fin n => (i : ℕ) < j + 1) = Finset.univ.filter fun i => i ≤ j := by
        ext i; simp [Nat.lt_succ_iff]
      rw [h2 j s hs, psEig, e, hs, map_prod ι, map_prod ι, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun i _ => ?_
      rw [map_mul, map_mul, ι.apply_symm_apply, map_inv₀, map_inv₀, map_pow, map_natCast, ← resCard_eq_normV]
      rfl
private theorem eig_det {n : ℕ} {R Γ : Type} [CommRing R] [Group Γ] [TopologicalSpace Γ] {l : ℕ} [Fact l.Prime] (y : R →+* Qbar l)
    (D : W.GDet n R Γ) (r : Γ →* GL (Fin n) (Qbar l)) (hr : Continuous r) (S : Set Γ) (hS : Dense S)
    (hD : ∀ i, Continuous fun g => y (D.lam i (MonoidAlgebra.single g 1)))
    (h : ∀ g ∈ S, (D.chi (MonoidAlgebra.single g 1)).map y = (r g : Matrix (Fin n) (Fin n) (Qbar l)).charpoly) :
    D.map y = W.GDet.ofRep (W.mat r) := by
  refine AlgebraTools.Det.extDense _ _ S hS (fun i _ => (hD i).congr fun g => ?_)
    (fun i _ => AlgebraTools.Det.repCont _ (Units.continuous_val.comp hr) i) fun g hg => ?_
  · simp [W.GDet.lam, eig_chi_map]
  · rw [eig_chi_map, (AlgebraTools.Det.repApi _).2.1]
    exact h g hg
private theorem eig_ord (hG : GlobalTheory.Published.GlobalArtinReciprocity) {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω]
    [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {n : ℕ} {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver B w)
    (hl : ((l : ℕ) : 𝓞 F) ∈ w.asIdeal) (a : Weil h →* (w.adicCompletion F)ˣ) (ha : IsLocalArtin h a) (ι : Qbar l ≃+* ℂ)
    (lam : Wt F l n) (ω : Fin n → (w.adicCompletion F)ˣ →* ℂˣ) (hω : ∀ i, IsSmoothChar (ω i)) {R : Type} [CommRing R]
    (y : R →+* Qbar l) (ψ : Fin n → Dec (F := F) B →* Rˣ) (hψ : ∀ i, Continuous fun g => y (ψ i g : R))
    (ε : Dec (F := F) B →* Rˣ) (he : ∀ g, y (ε g : R) = (cycBar F Ω l (g : G F Ω) : Qbar l))
    (t : Fin n → Uo (w.adicCompletion F) → R) (u : Fin n → R)
    (u1 : ∀ i (s : Weil h) (g : Dec (F := F) B) (x : Uo (w.adicCompletion F)), (g : G F Ω) = (s : G F Ω) → a s = x →
      (ψ i g * ε g ^ (i : ℕ) : Rˣ) * t i x = 1)
    (u2 : ∀ (j : Fin n) (s : Weil h) (g : Dec (F := F) B), (g : G F Ω) = (s : G F Ω) → a s = Hi.unif _ →
      ((∏ i with i ≤ j, ψ i g * ε g ^ (i : ℕ) : Rˣ) : R) = u j)
    (h1 : ∀ i (x : Uo (w.adicCompletion F)), (ω i x : ℂ) *
      ι (y (t i x) / algPow w (lowW lam i) ((x : (w.adicCompletion F)ˣ) : w.adicCompletion F)) = 1)
    (h2 : ∀ j : Fin n, ι (y (u j)) = (ι (∏ i ∈ Finset.univ.filter fun i : Fin n => (i : ℕ) < j + 1,
        algPow w (lowW lam i) ((Hi.unif (w.adicCompletion F) : (w.adicCompletion F)ˣ) : w.adicCompletion F)))⁻¹ * psEig ω (j + 1))
    (i : Fin n) : OrdChar ι a (ω i) (htW lam i) (W.pushCh y (ψ i)) := by
  refine ⟨hω i, Units.continuous_iff.2 ⟨hψ i, ((hψ i).comp continuous_inv).congr fun g => by simp⟩, fun s g hg _ => ?_⟩
  obtain rfl : g = Subgroup.inclusion (Weil_le_Dec h) s := Subtype.ext hg
  refine eig_loc hG h hl a ha ι lam ω
    (fun i => ((Units.coeHom _).comp (W.pushCh y (ψ i))).comp (Subgroup.inclusion (Weil_le_Dec h)))
    (fun i s hs => ?_) (fun j s hs => ?_) i s
  · have e1 := congrArg y (u1 i s (Subgroup.inclusion (Weil_le_Dec h) s) ⟨_, hs⟩ rfl rfl)
    have e2 := congrArg ι.symm (h1 i ⟨_, hs⟩)
    rw [map_mul, Units.val_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, he, map_one, Subgroup.coe_inclusion] at e1
    rw [map_mul, ι.symm_apply_apply, map_one, mul_div_assoc', div_eq_one_iff_eq (eig_ne _ _ _)] at e2
    change y (ψ i (Subgroup.inclusion (Weil_le_Dec h) s) : R) * _ * _ = _
    rw [← e2]
    linear_combination (ι.symm (ω i (a s) : ℂ)) * e1
  · refine Eq.trans (congrArg ι (Eq.trans ?_ (congrArg y (u2 j s (Subgroup.inclusion (Weil_le_Dec h) s) rfl hs)))) (h2 j)
    rw [Units.coe_prod, map_prod]
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Units.val_mul, map_mul, Units.val_pow_eq_pow_val, map_pow, he]
    rfl
private theorem eig_pt {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime]
    {n : ℕ} {c : Coef l} (H : HSet L Ω l n c) (R : Type) [CommRing R] [Algebra c.O R] [Alg.IsCO c.O R] :
    Fact (∀ y : R →ₐ[c.O] Qbar l, (∀ (Γ : Type) [TopologicalSpace Γ] (f : Γ → R), Alg.AdicCont (maximalIdeal R) f → Continuous fun g => y.toRingHom (f g)) ∧
      ∀ (v : H.V) (g : Dec (F := L) (H.pl v)), y.toRingHom (H.epsV R v g : R) = (cycBar L Ω l (g : G L Ω) : Qbar l)) := by
  refine ⟨fun y => ?_⟩
  obtain ⟨-, b, b1, b0, hb⟩ := (GradeZeroInterpolatingElement.coPt c R).1 y
  exact ⟨fun Γ _ f hf => eig_cont _ y.toRingHom b b1 b0 hb hf,
    fun v g => (y.commutes (algebraMap ℤ_[l] c.O (cycZ L Ω l (g : G L Ω) : ℤ_[l]))).trans rfl⟩

theorem UpperTheory.V.Hi.core_eigen_of_weight_char_hecke_level :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ), ∀ (a : H.Op → c.O) (K : H.Lev) [Fact (CommOn (H.MK θ a K) (H.op A))] [Alg.IsCO c.O (H.TK θ a K)], ∀ (D : W.GDet n (H.TK θ a K) H.Gq) (ψ : ∀ v, Fin n → Dec (F := L) (H.pl v) →* (H.TK θ a K)ˣ), H.IsUniv θ a K (maximalIdeal _) D ψ →
    ∀ (y : H.TK θ a K →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (Y : H.PartAltAlt ι lam ξ) (F : Fin H.m → H.X.Fn ℂ d), F ∈ Y.Y → F ≠ 0 → (∀ w j, H.opC ι lam d (.inl (w, j)) F = ι (y (H.gen θ a K (.inl (w, j)))) • F) → D.map y.toRingHom = W.GDet.ofRep (W.mat Y.r) ∧ ∀ v (ω : Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ), (∀ i, IsSmoothChar (ω i)) → (∀ i (u : Uo ((H.Sl v).adicCompletion L)), (ω i u : ℂ) * ι (H.finPart θ (y.toRingHom.comp (algebraMap A _)) lam v i u) = 1) → (∀ j : Fin n, ι (y (H.gen θ a K (.inr (v, j)))) = (H.lowVal ι lam v (j + 1))⁻¹ * psEig ω (j + 1)) → ∀ i, OrdChar ι (H.art v) (ω i) (htW lam i) (W.pushCh y.toRingHom (ψ v i)) := by
  intro hN L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ _ ι a K _ _ D ψ hU y lam d ξ Y F hF hF0 hev
  obtain ⟨hc, he⟩ := (eig_pt H (H.TK θ a K)).out y
  refine ⟨eig_det _ D Y.r Y.cont _ hH.dense (fun i => hc _ _ (hU.cont i)) ?_,
    fun v ω hω h1 h2 i => ?_⟩
  · rintro _ ⟨w, hw, B, σ, hB, hσ, rfl⟩
    rw [hU.frob ⟨w, hw⟩ B σ hB hσ]
    refine Polynomial.map_injective ι.toRingHom ι.injective ?_
    rw [Polynomial.map_map]
    refine (eig_pol _ n _ _ (Y.a ⟨w, hw⟩) fun j hj => ?_).trans (Y.frob ⟨w, hw⟩ B σ hB hσ).symm
    unfold HSet.genW
    split_ifs with h
    · have e := hev ⟨w, hw⟩ ⟨j - 1, h.2⟩
      have e' := Y.sph ⟨w, hw⟩ (j - 1 + 1) F hF
      have e2 := smul_left_injective ℂ hF0 (e.symm.trans e')
      rw [show j - 1 + 1 = j by omega] at e2
      exact e2
    · rw [show j = 0 by omega, Y.a_zero, map_one]
  · have h3 := eig_ord hN.aut.art (H.ovr v) (hH.Sl_over v) (H.art v) (hH.art_spec v) ι lam ω hω _ (ψ v)
      (fun i => hc _ _ (hU.ψ_cont v i)) _ (he v)
    have h4 := h3 (fun i x => algebraMap A (H.TK θ a K) (θ (eV n H.Sl v i x))) (fun j => H.gen θ a K (.inr (v, j)))
      (hU.ψ_unit v) (hU.ψ_unif v) h1 h2
    exact h4 i
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TCoreUp
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Polynomial ValuativeRel IsLocalRing GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V UpperTheory.V.Hi
open UpperTheory.V.HV (Coef)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
private theorem up_list {σ : Type} [DecidableEq σ] {G : σ → Type} [∀ v, Group (G v)] (g : ∀ v, G v) (w : σ) (s : List σ)
    (hs : s.Nodup) : (s.map fun v => Pi.mulSingle v (g v)).prod w = if w ∈ s then g w else 1 := by
  induction s with
  | nil => simp
  | cons v s ih =>
    rw [List.nodup_cons] at hs
    rw [List.map_cons, List.prod_cons, Pi.mul_apply, ih hs.2]
    by_cases h : w = v
    · subst h; simp [hs.1]
    · simp [h]
section
variable {L Ω : Type} [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] {l : ℕ} [Fact l.Prime] {n : ℕ}
  {c : Coef l} (H : HSet L Ω l n c) (ι : Qbar l ≃+* ℂ)
private theorem up_VV (d : ℕ) (v v' : H.V) (h : v ≠ v') (g g') (F) :
    H.atV d v g (H.atV d v' g' F) = H.atV d v' g' (H.atV d v g F) := by
  classical
  change (H.X.rpF ℂ d H.m (Pi.mulSingle v g) * H.X.rpF ℂ d H.m (Pi.mulSingle v' g')) F =
    (H.X.rpF ℂ d H.m (Pi.mulSingle v' g') * H.X.rpF ℂ d H.m (Pi.mulSingle v g)) F
  rw [← map_mul, ← map_mul, (Pi.mulSingle_commute (f := fun v : H.V => GLw n (H.Sl v)) h g g').eq]
private theorem up_PA (d : ℕ) (g u) (F) :
    H.X.rpF ℂ d H.m g (H.X.raF d (H.τC ι) u F) = H.X.raF d (H.τC ι) u (H.X.rpF ℂ d H.m g F) := by
  funext i x k
  change (H.X.ra (H.τC ι) u (fun y j => F j y k) (x * (1, g))) i =
    H.X.ra (H.τC ι) u (fun y j => F j (y * (1, g)) k) x i
  rw [Frame.ra_apply, Frame.ra_apply]
  simp [mul_assoc]
private theorem up_vec (hL : _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis) (hH : H.Ax) {lam : Wt L l n} {d : ℕ} {ξ : GV n H.Sl →* GL (Fin d) ℂ}
    (Y : H.PartAltAlt ι lam ξ) (K : H.Lev) (hK : ∀ q, fixd (Y.σq q).ρ (K.1 q) ≠ ⊥)
    (ω : ∀ v, Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ) (hω : ∀ v, Nonempty ((Y.σl v).ρ.Equiv (PS (ω v)))) (e : ℕ)
    (he : ∀ v i, ∀ y ∈ Uc _ (e + 1), ω v i y = 1)
    (φ : ∀ v, (glIwa ((H.Sl v).adicCompletion L) n).T →* ℂˣ) (hφ : ∀ v, IsInvOn (φ v) (ω v)) :
    ∃ F ∈ Y.Y, F ≠ 0 ∧ (∀ v, F ∈ Up.ordC (H.atV d v) e (φ v) (psEig (ω v))) ∧
      ∀ q, F ∈ fixd (H.atW ι d (H.wq q)) (K.1 q) := by
  refine Exists.imp (fun F h => ⟨h.1, h.2.1, fun v => h.2.2 (.inl v), fun q => h.2.2 (.inr q)⟩) (Up.meet (I := H.V ⊕ H.Q)
    (Sum.elim (fun v => Set.range (H.atV d v)) fun q => Set.range (H.atW ι d (H.wq q)))
    (Sum.elim (fun v => Up.ordC (H.atV d v) e (φ v) (psEig (ω v))) fun q => fixd (H.atW ι d (H.wq q)) (K.1 q))
    Y.Y Y.ne ?_ ?_ ?_)
  · rintro (v | q) _ ⟨g, rfl⟩
    · exact Up.isoStab (Y.isoL v) g
    · exact Up.isoStab (Y.isoQ q) g
  · rintro (v | q) (v' | q') hne _ ⟨g, rfl⟩
    · exact Up.ordMap _ _ _ (fun g' F => up_VV H d v' v (fun h => hne (by rw [h])) g g' F) _ _ _
    · exact Up.ordMap _ _ _ (fun g' F => (up_PA H ι d _ _ F).symm) _ _ _
    · exact Up.fixMap (H.atW ι d (H.wq q)) (H.atW ι d (H.wq q)) _ (fun g' F => up_PA H ι d _ _ F) _
    · refine Up.fixMap _ _ _ (fun g' F => ?_) _
      change (H.X.raF d (H.τC ι) _ * H.X.raF d (H.τC ι) _) F = (H.X.raF d (H.τC ι) _ * H.X.raF d (H.τC ι) _) F
      rw [← map_mul, ← map_mul]
      exact congrArg (fun u => H.X.raF d (H.τC ι) u F) (hH.Q_Q q q' (fun h => hne (by rw [h])) g' g).eq.symm
  · rintro (v | q) Z hZ hne hst
    · obtain ⟨p, hp1, hp2, hp3⟩ := Up.isoSub (Y.isoL v) Z hZ hne fun g => hst _ ⟨g, rfl⟩
      obtain ⟨u, hu1, hu2, hu3⟩ := _root_.UpperTheory.V.Hi.exists_ne_zero_mem_eig_uOp_eq_psEig_smul_of_equiv_ps hL _ n _ (Y.σl v).ρ (ω v) (hω v) e (he v) (φ v) (hφ v)
      refine (Submodule.ne_bot_iff _).2 ⟨p u, ⟨hp2 ⟨u, rfl⟩, ?_⟩, fun h => hu2 (hp3 (by rw [h, map_zero]))⟩
      exact Up.ordMap _ _ p hp1 _ _ _ u ((Up.mem_ordC _ _ _ _ _).2 ⟨hu1, hu3⟩)
    · obtain ⟨p, hp1, hp2, hp3⟩ := Up.isoSub (Y.isoQ q) Z hZ hne fun g => hst _ ⟨g, rfl⟩
      obtain ⟨u, hu1, hu2⟩ := (Submodule.ne_bot_iff _).1 (hK q)
      exact (Submodule.ne_bot_iff _).2 ⟨p u, ⟨hp2 ⟨u, rfl⟩, Up.fixMap _ _ p hp1 _ u hu1⟩,
        fun h => hu2 (hp3 (by rw [h, map_zero]))⟩
private theorem up_ord {A : Type} [CommRing A] (θ : H.X.I.T →* Aˣ) (x : A →+* Qbar l)
    {lam : Wt L l n} {d : ℕ} {ξ : GV n H.Sl →* GL (Fin d) ℂ} (K : H.Lev)
    (ω : ∀ v, Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ) (e : ℕ)
    (hω : ∀ v i (u : Uo ((H.Sl v).adicCompletion L)), (ω v i u : ℂ) * ι (H.finPart θ x lam v i u) = 1)
    (hn : ∀ v (j : Fin n), ‖ι.symm ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1))‖ = 1)
    (φ : ∀ v, (glIwa ((H.Sl v).adicCompletion L) n).T →* ℂˣ) (hφ : ∀ v, IsInvOn (φ v) (ω v))
    (F : Fin H.m → H.X.Fn ℂ d) (hB : F ∈ H.Big ι ξ) (hV : ∀ v, F ∈ Up.ordC (H.atV d v) e (φ v) (psEig (ω v)))
    (hQ : ∀ q, F ∈ fixd (H.atW ι d (H.wq q)) (K.1 q)) :
    F ∈ H.OrdAt θ ι x lam ξ K e ∧ ∀ v (j : Fin n),
      H.opC ι lam d (.inr (v, j)) F = ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1)) • F := by
  classical
  simp only [Up.mem_ordC] at hV
  let I := fun v : H.V => glIwa ((H.Sl v).adicCompletion L) n
  have hN : F ∈ fixd (H.X.rpF ℂ d H.m) H.X.I.N := Up.fixPi _ (fun v => (I v).N) F fun v => (hV v).1.1
  have hNm : F ∈ fixd (H.X.rpF ℂ d H.m) (H.X.I.Nm e) := Up.fixPi _ (fun v => (I v).Nm e) F fun v => (hV v).1.2.1
  have hlev : F ∈ fixd (H.X.raF d (H.τC ι)) (H.lev K) := by
    intro u hu
    let St : Subgroup H.X.Ub :=
      (MulAction.stabilizer (Module.End ℂ (Fin H.m → H.X.Fn ℂ d))ˣ F).comap (H.X.raF d (H.τC ι)).toHomUnits
    have : H.lev K ≤ St := sup_le (fun u hu => hB.2 u hu) (iSup_le fun q => by
      rintro _ ⟨g, hg, rfl⟩
      exact hQ q g hg)
    exact this hu
  have hCl : F ∈ H.ClAt θ ι x lam ξ K e := by
    refine ⟨⟨⟨⟨hB, hlev⟩, hN⟩, hNm⟩, ?_⟩
    simp only [SetLike.mem_coe, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
    intro v i y
    have h1 := (hV v).1.2.2 (eT _ n i y)
    rw [hφ v i y, inv_inv, eq_inv_of_mul_eq_one_left (hω v i y)] at h1
    exact h1
  have hz : ∀ v, (I v).uOp (H.atV d v) (I v).z F = ((List.range n).map (psEig (ω v))).prod • F := by
    intro v
    have h1 := (glBridge ((H.Sl v).adicCompletion L) n _ (H.atV d v)).2.2.2.2.2.2.2.2.1
    have h2 := (Up.uOpList (I v) (H.atV d v) F (hV v).1.1 (al _ n) (psEig (ω v)) (List.range n)
      fun j hj => ⟨al_mem _ n j, (hV v).2 j (List.mem_range.1 hj).le⟩).2
    rwa [← h1] at h2
  have hZ := (Up.uOpList (piIwa I) (H.X.rpF ℂ d H.m) F hN (fun v => Pi.mulSingle v (I v).z)
    (fun v => ((List.range n).map (psEig (ω v))).prod) Finset.univ.toList
    fun v _ => ⟨Up.singleP I v _ (I v).z_mem, (Up.uOpPi I _ v _ (I v).z_mem F hN).trans (hz v)⟩).2
  have hzz : (Finset.univ.toList.map fun v => (Pi.mulSingle v (I v).z : GV n H.Sl)).prod = H.X.I.z := by
    funext w
    rw [up_list (fun v => (I v).z) w _ (Finset.nodup_toList _), if_pos (by simp)]
    rfl
  rw [hzz, Finset.prod_map_toList] at hZ
  have hl : ∀ v, ((List.range n).map (psEig (ω v))).prod = ∏ j ∈ Finset.range n, psEig (ω v) j := fun v => rfl
  simp only [hl] at hZ
  refine ⟨?_, fun v j => ?_⟩
  · refine Submodule.mem_iSup_of_mem
      ⟨∏ v, ∏ j ∈ Finset.range n, (H.lowVal ι lam v j)⁻¹ * psEig (ω v) j, ?_⟩ ⟨hCl, ?_⟩
    · rw [map_prod, norm_prod]
      refine Finset.prod_eq_one fun v _ => ?_
      rw [map_prod, norm_prod]
      refine Finset.prod_eq_one fun j hj => ?_
      rcases j with _ | j
      · simp [HSet.lowVal, psEig]
      · exact hn v ⟨j, by have := Finset.mem_range.1 hj; omega⟩
    · refine Module.End.eigenspace_le_maxGenEigenspace (Module.End.mem_eigenspace_iff.2 ?_)
      change (∏ v, ∏ j ∈ Finset.range n, H.lowVal ι lam v j)⁻¹ • (piIwa I).uOp (H.X.rpF ℂ d H.m) H.X.I.z F = _
      rw [hZ, smul_smul]
      simp only [Finset.prod_mul_distrib, Finset.prod_inv_distrib]
  · change (H.lowVal ι lam v (j + 1))⁻¹ • (piIwa I).uOp (H.X.rpF ℂ d H.m) (Pi.mulSingle v (al _ n (j + 1))) F = _
    rw [Up.uOpPi I _ v _ (al_mem _ n _) F hN, ← smul_smul]
    exact congrArg _ ((hV v).2 _ j.2)
end
theorem UpperTheory.V.Hi.coreUp_alt :
    _root_.GlobalTheory.Mem.LiteralAutomorphy.LiteratureRankNHypothesis → ∀ (L Ω : Type) [Field L] [NumberField L] [Field Ω] [Algebra L Ω] [IsAlgClosure L Ω] (l : ℕ) [Fact l.Prime] (n : ℕ) (c : Coef l) (H : HSet L Ω l n c), H.Ax →
    ∀ (A : Type) [CommRing A] [Algebra c.O A] [Alg.IsCO c.O A] (θ : H.X.I.T →* Aˣ), H.IsWt θ →
    ∀ (ι : Qbar l ≃+* ℂ), ∀ (x : A →ₐ[c.O] Qbar l) (lam : Wt L l n) (d : ℕ) (ξ : GV n H.Sl →* GL (Fin d) ℂ) (c0 : ℕ) (sp : H.X.Fn A H.m → Fin H.m → H.X.Fn ℂ d), H.IsSpec θ ι x.toRingHom lam ξ c0 sp →
    ∀ (Y : H.PartAltAlt ι lam ξ) (K : H.Lev), (∀ q, fixd (Y.σq q).ρ (K.1 q) ≠ ⊥) → ∀ ω : ∀ v, Fin n → ((H.Sl v).adicCompletion L)ˣ →* ℂˣ, (∀ v, Nonempty ((Y.σl v).ρ.Equiv (PS (ω v)))) → (∀ v i (u : Uo ((H.Sl v).adicCompletion L)), (ω v i u : ℂ) * ι (H.finPart θ x.toRingHom lam v i u) = 1) → ∀ a : H.Op → c.O, (∀ w (j : Fin n), ‖ι.symm (Y.a w (j + 1)) - algebraMap c.O (Qbar l) (a (.inl (w, j)))‖ < 1) → (∀ v (j : Fin n), ‖ι.symm ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1))‖ = 1 ∧ ‖ι.symm ((H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1)) - algebraMap c.O (Qbar l) (a (.inr (v, j)))‖ < 1) → ∀ [Fact (CommOn (H.MK θ a K) (H.op A))], H.MK θ a K ≠ ⊥ ∧ ∃ y : H.TK θ a K →ₐ[c.O] Qbar l, y.toRingHom.comp (algebraMap A _) = x.toRingHom ∧ (∀ w (j : Fin n), ι (y (H.gen θ a K (.inl (w, j)))) = Y.a w (j + 1)) ∧ ∀ v (j : Fin n), ι (y (H.gen θ a K (.inr (v, j)))) = (H.lowVal ι lam v (j + 1))⁻¹ * psEig (ω v) (j + 1) := by
  intro hL L Ω _ _ _ _ _ l _ n c H hH A _ _ _ θ hθ ι x lam d ξ c0 sp hsp Y K hK ω hω1 hω2 a ha1 ha2 hFact
  haveI : Finite (ResidueField c.O) := (UpperTheory.V.abelian₂.dvr_finite l c.O).2.1
  haveI : IsCNL A := IsCNL.ofCO c.O A
  obtain ⟨hC, hfin, hfree, -⟩ := hiComm L Ω l n c H hH A θ hθ K
  choose φ hφ using fun v => Up.exInv (ω v)
  obtain ⟨F, hF, h0, hV, hQ⟩ := up_vec H ι hL hH Y K hK ω hω1 c0 (fun v i y hy => by
    have h := hω2 v i ⟨y, Up.Uc_le _ hy⟩
    rw [hsp.triv v i _ hy, map_one, mul_one] at h
    exact Units.ext h) φ hφ
  obtain ⟨hO, hU⟩ := up_ord H ι θ x.toRingHom K ω c0 hω2 (fun v j => (ha2 v j).1) φ hφ F (Y.le hF) hV hQ
  rw [← hsp.span K c0 le_rfl] at hO
  have hx2 : ∀ b ∈ maximalIdeal A, ‖x.toRingHom b‖ < 1 := Up.normLt x
  have hx1 : ∀ b, ‖x.toRingHom b‖ ≤ 1 := by
    intro b
    obtain ⟨o, ho⟩ := Alg.IsCO.res_surj (O := c.O) b
    have h1 : ‖x (algebraMap c.O A o)‖ ≤ 1 := by
      rw [x.commutes]
      exact (Up.intIff _).1 ((Algebra.IsIntegral.isIntegral (R := ℤ_[l]) o).map c.O.val)
    have h2 : x.toRingHom b = x.toRingHom (b - algebraMap c.O A o) + x (algebraMap c.O A o) := by simp
    rw [h2]
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le (hx2 _ ho).le h1)
  haveI : Fact (CommOn (locPart (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) fun i => algebraMap c.O A (a i)) (H.op A)) := hFact
  obtain ⟨hne, y, hy1, hy2⟩ := Up.eigPt (H.X.Ord (H.τA A) θ (H.lev K)) (H.op A) hC ι x.toRingHom hx1 hx2 sp
    (hsp.add K) (hsp.smul K) (hsp.indep K) (H.opC ι lam d) (hsp.op K) F hO h0
    (Sum.elim (fun p => Y.a p.1 (p.2 + 1)) fun p => (H.lowVal ι lam p.1 (p.2 + 1))⁻¹ * psEig (ω p.1) (p.2 + 1))
    (by
      rintro (⟨w, j⟩ | ⟨v, j⟩)
      · exact Y.sph w _ F hF
      · exact hU v j)
    (fun i => algebraMap c.O A (a i))
    (by
      rintro (⟨w, j⟩ | ⟨v, j⟩)
      · exact (x.commutes _).symm ▸ ha1 w j
      · exact (x.commutes _).symm ▸ (ha2 v j).2)
  refine ⟨hne, ⟨y, fun o => ?_⟩, RingHom.ext hy1, fun w j => hy2 (.inl (w, j)),
    fun v j => hy2 (.inr (v, j))⟩
  refine Eq.trans (congrArg y ?_) ((hy1 _).trans (x.commutes o))
  exact Subtype.ext (LinearMap.ext fun f => (algebraMap_smul A o f).symm)
end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ThresholdArguments.DenseThresholdCases.TPlainAtW
section
set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain ValuativeRel Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.PRep
open UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Dict
open UpperTheory.V.W (Plc Lp)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
namespace UpperTheory.V.Z.Sym.W
private theorem ratios {G : Type*} [CommGroup G] (a p : G) (h1 : p ≠ 1) (h2 : a ≠ p) (h3 : a ≠ p⁻¹)
    (h4 : a ^ 2 ≠ p) (h5 : a ^ 2 ≠ p⁻¹) (i j : Fin 3) :
    (![a, 1, a⁻¹] : Fin 3 → G) i ≠ (![a, 1, a⁻¹] : Fin 3 → G) j * p := by
  intro e
  fin_cases i <;> fin_cases j <;> simp at e
  · exact h1 e
  · exact h2 e
  · exact h4 (by rw [pow_two]; nth_rewrite 1 [e]; simp)
  · exact h3 (eq_inv_of_mul_eq_one_left e.symm)
  · exact h1 e.symm
  · exact h2 (inv_mul_eq_one.mp e.symm)
  · have e' : a ^ 2 * p = 1 := by rw [pow_two, mul_assoc, ← e]; simp
    exact h5 (eq_inv_of_mul_eq_one_left e')
  · exact h3 (by simpa using congrArg (·⁻¹) e)
  · exact h1 e
private theorem absOne_ne (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] :
    absPow k 1 ≠ 1 := by
  intro h
  have e : absPow k ((1 : ℝ) : ℂ) = absPow k ((0 : ℝ) : ℂ) := by
    simpa [absPow_zero] using h
  obtain ⟨ϖ, hϖ⟩ := GlobalTheory.LocGL.exists_uniformizer k
  have h1 : nabs k ϖ ≠ 1 := fun he => ValuativeRel.uniformizer_lt_one.ne (hϖ ▸ (nabs_eq_one_iff ϖ).1 he)
  have h2 : nabs k ϖ ^ (1 : ℝ) = nabs k ϖ ^ (0 : ℝ) := by
    have hx := val_absPow_ofReal k 1 ϖ
    have hy := val_absPow_ofReal k 0 ϖ
    rw [e] at hx
    exact_mod_cast hx.symm.trans hy
  have h3 := congrArg Real.log h2
  rw [Real.log_rpow (nabs_pos' k ϖ), Real.log_rpow (nabs_pos' k ϖ)] at h3
  exact one_ne_zero (mul_right_cancel₀ (Real.log_ne_zero_of_pos_of_ne_one (nabs_pos' k ϖ) h1) h3)
end UpperTheory.V.Z.Sym.W
theorem UpperTheory.V.Z.Sym.W.plain_at_w_statement :
    _root_.UpperTheory.V.Z.Sym.W.PlainAtWAlt := by
  intro hL L _ _ _ σ π hσ hl w hw a ha ⟨hs, τ₀, h₀, hq⟩ τ hτ
  have hc := hl.comp w hw τ hτ
  obtain ⟨e⟩ := UpperTheory.building_component_uniqueness L 3 σ hσ w hw _ _ _ _ h₀ hc
  have hq' : IsSubquotient τ.ρ (prinSeries ![a, 1, a⁻¹]) :=
    (IsSubquotient.of_surjective e.toIntertwiningMap e.surjective).trans hq
  have hp := absOne_ne (Kw w)
  have n1 := ha 1 (Or.inl rfl) 1 (Or.inl rfl)
  have n2 := ha 1 (Or.inl rfl) (-1) (Or.inr rfl)
  have n3 := ha 2 (Or.inr rfl) 1 (Or.inl rfl)
  have n4 := ha 2 (Or.inr rfl) (-1) (Or.inr rfl)
  simp only [pow_one, Int.cast_one, Int.cast_neg, absPow_neg] at n1 n2 n3 n4
  exact _root_.UpperTheory.V.Z.Sym.W.plain_of_statement hL L 3 w τ _ hs hq' (ratios a _ hp n1 n2 n3 n4)
end
end

