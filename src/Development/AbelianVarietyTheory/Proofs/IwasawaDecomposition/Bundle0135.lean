module

public import Mathlib
public import Formalism.LocalToGlobal.KernelLattices.ThDistC
public import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0113
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0118
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0117
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0744
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0130
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0057
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FixedCoefficientFieldInComplex
public import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.PublishedTheorems.WeberRayClassFields.WeberRayFieldSt
public import Development.AbelianVarietyTheory.Proofs.JetHarmonics.Bundle0010
public import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0026
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0120
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0126
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0128
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0129

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FinAlgJetSet
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker GlobalTheory.Mem.Col2.JetEx

namespace GlobalTheory.Mem.Col2.JetFin

theorem finAlg_range {E : Type} [Field E] [NumberField E] (f : E →+* ℂ) : FinAlg (Set.range f) := by
  classical
  let b := Module.finBasis ℚ E
  refine (finAlg_of_finite (T := Set.range (f ∘ b)) (Set.finite_range _) ?_).closure.mono ?_
  · rintro _ ⟨i, rfl⟩
    exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) (b i)).algHom f.toRatAlgHom
  · rintro _ ⟨x, rfl⟩
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← b.sum_repr x, map_sum]
    refine sum_mem fun i _ => ?_
    rw [map_rat_smul, Rat.smul_def]
    exact mul_mem (SubfieldClass.ratCast_mem _ _) (Subfield.subset_closure ⟨i, rfl⟩)

variable {X : Fields} (A : Amb X) {a b : ℕ} (S : Finset (HeightOneSpectrum (𝓞 X.E)))

theorem thInd_congr (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (c : ℕ) (x x' : HomE X.E a b)
    (h : x - x' ∈ mulLat c (homAt S N N')) : A.thInd S N N' c x = A.thInd S N N' c x' := by
  unfold Amb.thInd Amb.liftW
  rw [isLift_congr A S N N' c x x' h]

theorem finite_thInd (N : Submodule (𝓞 X.E) (Sp X.E a)) (N' : Submodule (𝓞 X.E) (Sp X.E b)) (M c : ℕ)
    (hN : IsSdLat N) (hN' : IsSdLat N') (hM : 0 < M) (hc : 0 < c) :
    (A.thInd S N N' c '' (divLat M (homAt S N N') : Set (HomE X.E a b))).Finite := by
  have := (GlobalTheory.SemilocalClasses.finite_card_classes X.E a b S N N' M c hN.1 hN'.1 hM hc).1
  refine (Set.finite_range fun q : (↥(divLat M (homAt S N N')) ⧸ (mulLat c (homAt S N N')).comap (divLat M (homAt S N N')).subtype) =>
    A.thInd S N N' c (Quotient.out q).1).subset ?_
  rintro _ ⟨x, hx, rfl⟩
  refine ⟨Submodule.Quotient.mk ⟨x, hx⟩, thInd_congr A S N N' c _ _ ?_⟩
  have := (Submodule.Quotient.eq ((mulLat c (homAt S N N')).comap (divLat M (homAt S N N')).subtype)).1
    (Quotient.out_eq (Submodule.Quotient.mk ⟨x, hx⟩ : (↥(divLat M (homAt S N N')) ⧸ (mulLat c (homAt S N N')).comap (divLat M (homAt S N N')).subtype)))
  exact this

noncomputable def pullLin (γ : Sp X.E a ≃ₗ[X.E] Sp X.E a) (γ' : Sp X.E b ≃ₗ[X.E] Sp X.E b) : VCx X.Tau a b →ₗ[ℂ] VCx X.Tau a b where
  toFun := A.pullV a b γ γ'
  map_add' z w := by
    funext τ i j
    simp only [Amb.pullV, Pi.add_apply, mul_add, add_mul, Finset.sum_add_distrib]
  map_smul' t z := by
    funext τ i j
    simp only [Amb.pullV, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => by ring

theorem finAlg_jetSet : ∀ (X : Fields) (A : Amb X) (a b : ℕ) (S : Finset (HeightOneSpectrum (𝓞 X.E))) (M n : ℕ), X.Ok → 0 < M → A.ESmooth a b → A.ThIndEq a b S M → A.ChiLaw a b → JetAlg A a b S M → (∀ τ, IsAlgebraic ℚ (A.cD τ)) → FinAlg (jetSet A a b S M n) := by
  intro X A a b S M n hX hM hE hT hC hJ hD
  classical
  obtain ⟨Ta, hTa, hTa'⟩ := GlobalTheory.Mem.Col2.JetEx.exists_finset_sdLat_reps X hX a
  obtain ⟨Tb, hTb, hTb'⟩ := GlobalTheory.Mem.Col2.JetEx.exists_finset_sdLat_reps X hX b
  let Z₀ : Set ℂ := ⋃ N ∈ (Ta : Set _), ⋃ N' ∈ (Tb : Set _), ⋃ c ∈ (M.divisors : Set ℕ),
    ⋃ G ∈ A.thInd S N N' c '' (divLat M (homAt S N N') : Set (HomE X.E a b)),
      ⋃ e ∈ {e : DVar X.Tau a b →₀ ℕ | e.degree ≤ n}, {(A.chiF a b N N')⁻¹ * derivAt0 G e}
  have hZ₀ : FinAlg Z₀ := by
    refine finAlg_biUnion Ta.finite_toSet fun N hN => finAlg_biUnion Tb.finite_toSet fun N' hN' =>
      finAlg_biUnion (Finset.finite_toSet _) fun c hc => ?_
    have hc' : c ∣ M := Nat.dvd_of_mem_divisors hc
    have hc0 : 0 < c := Nat.pos_of_mem_divisors hc
    refine finAlg_biUnion (finite_thInd A S N N' M c (hTa N hN) (hTb N' hN') hM hc0) ?_
    rintro _ ⟨x, hx, rfl⟩
    refine finAlg_biUnion (Finsupp.finite_of_degree_le n) fun e _ => finAlg_of_finite (Set.finite_singleton _) ?_
    rintro _ rfl
    exact hJ N N' c x ⟨hTa N hN, hTb N' hN', hc0, hc', hx⟩ e
  have h1 : FinAlg (Set.range A.cD) := finAlg_of_finite (Set.finite_range _) (by rintro _ ⟨τ, rfl⟩; exact hD τ)
  have h2 : FinAlg (⋃ τ ∈ (Set.univ : Set X.Tau), Set.range (X.embC A.σ₀ τ)) :=
    finAlg_biUnion Set.finite_univ fun τ _ => finAlg_range _
  refine ((hZ₀.union h1).union h2).closure.mono ?_
  set K₀ := Subfield.closure ((Z₀ ∪ Set.range A.cD) ∪ ⋃ τ ∈ (Set.univ : Set X.Tau), Set.range (X.embC A.σ₀ τ)) with hK₀
  have hemb : ∀ τ x, X.embC A.σ₀ τ x ∈ K₀ := fun τ x =>
    Subfield.subset_closure (Or.inr (Set.mem_biUnion (Set.mem_univ τ) ⟨x, rfl⟩))
  have hcD : ∀ τ, A.cD τ ∈ K₀ := fun τ => Subfield.subset_closure (Or.inl (Or.inr ⟨τ, rfl⟩))
  rintro _ ⟨N, N', c, x, e, hr, he, rfl⟩
  obtain ⟨N₀, hN₀, γ, rfl⟩ := hTa' N hr.1
  obtain ⟨N₀', hN₀', γ', rfl⟩ := hTb' N' hr.2.1
  obtain ⟨x₀, rfl⟩ : ∃ x₀ : HomE X.E a b, x = γ'.1.toLinearMap ∘ₗ x₀ ∘ₗ γ.1.symm.toLinearMap :=
    ⟨γ'.1.symm.toLinearMap ∘ₗ x ∘ₗ γ.1.toLinearMap, by ext v; simp⟩
  have hr₀ : InRange S M c N₀ N₀' x₀ :=
    ⟨hTa _ hN₀, hTb _ hN₀', hr.2.2.1, hr.2.2.2.1, (divLat_gmap_iff S M _ _ _ _ _).1 hr.2.2.2.2⟩
  have hth : A.thInd S (gmap γ.1 N₀) (gmap γ'.1 N₀') c (γ'.1.toLinearMap ∘ₗ x₀ ∘ₗ γ.1.symm.toLinearMap) =
      fun z => A.thInd S N₀ N₀' c x₀ (pullLin A γ.1 γ'.1 z) := funext (hT γ γ' N₀ N₀' c x₀ hr₀)
  have key : (A.chiF a b N₀ N₀')⁻¹ * derivAt0 (fun z => A.thInd S N₀ N₀' c x₀ (pullLin A γ.1 γ'.1 z)) e ∈ K₀ := by
    refine GlobalTheory.Mem.JetChain.derivAt0_comp_mem X.Tau a b n K₀ _ _ _ (indSmooth_of A a b S M hE N₀ N₀' c x₀ hr₀) ?_ ?_ e he
    · intro k τ i j
      show A.pullV a b γ.1 γ'.1 (coordX k) τ i j ∈ K₀
      unfold Amb.pullV
      refine sum_mem fun k' _ => sum_mem fun l _ => mul_mem (mul_mem (hemb _ _) ?_) (hemb _ _)
      unfold coordX
      split_ifs
      · exact one_mem _
      · exact zero_mem _
    · intro e' he'
      refine Subfield.subset_closure (Or.inl (Or.inl ?_))
      refine Set.mem_biUnion hN₀ (Set.mem_biUnion hN₀' (Set.mem_biUnion (x := c) ?_ (Set.mem_biUnion ⟨x₀, hr₀.2.2.2.2, rfl⟩
        (Set.mem_biUnion (x := e') he'.le rfl))))
      exact Finset.mem_coe.2 (Nat.mem_divisors.2 ⟨hr₀.2.2.2.1, hM.ne'⟩)
  show _ ∈ K₀
  rw [hth, hC γ γ' N₀ N₀' hr₀.1 hr₀.2.1, jetC, mul_inv, mul_assoc, mul_left_comm (A.chiF a b N₀ N₀')⁻¹]
  refine mul_mem (inv_mem (mul_mem (zpow_mem (prod_mem fun τ _ => hemb _ _) _) (zpow_mem (prod_mem fun τ _ => hemb _ _) _)))
    (mul_mem (prod_mem fun k _ => pow_mem (hcD _) _) key)

end GlobalTheory.Mem.Col2.JetFin
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasLatticeNormalFormOfBetween
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

noncomputable section

namespace GlobalTheory.Proof.hasLatticeNormalForm_of_between

open GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm GlobalTheory.Proof.normal_form_bounds_unfolding

section General

variable {E : Type} [Field E] [NumberField E] [StarRing E] {n c : ℕ}

omit [StarRing E] in
theorem intV_eN (P : HeightOneSpectrum (𝓞 E)) (N s : ℕ) : IntV P (Loc.eN E N s) := by
  intro l
  unfold Loc.eN
  split_ifs
  · exact intAt_one P
  · exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem read_bounds (P : HeightOneSpectrum (𝓞 E)) (j : ℕ) (h ρ : (Fin (n + c) → E) ≃ₗ[E] (Fin (n + c) → E))
    (e : Fin c → ℤ) (z : Fin n → E) (hρ : ρ ∈ Loc.R1 E n c) (h1 : IntHom P h.symm.toLinearMap)
    (h2 : IntHom P (((qOf P : E) ^ j) • h.toLinearMap)) (hL : (ρ * h) '' {v | IntV P v} = nfLat P n c e z) :
    (∀ i, -(j : ℤ) ≤ e i ∧ e i ≤ 0) ∧ (1 ≤ c → IntV P z) := by
  have hq := Proof.NormalFormAtPrime.qOf_ne_zero P
  have hmem : ∀ v, IntV P v → ρ v ∈ nfLat P n c e z := fun v hv => by
    rw [← hL]
    refine ⟨h.symm v, h1 v hv, ?_⟩
    change ρ (h (h.symm v)) = ρ v
    rw [h.apply_symm_apply]
  refine ⟨fun i => ⟨?_, ?_⟩, fun hc a => ?_⟩
  · obtain ⟨v, hv, hrv⟩ : nfGen (qOf P) n c e z i ∈ (ρ * h) '' {v | IntV P v} := hL ▸ nfGen_mem P e z i
    change ρ (h v) = _ at hrv
    have hU : h v ∈ Loc.Ufl E n c (i.1 + 1) := by
      have := hρ.2.1 _ _ (hrv ▸ nfGen_mem_Ufl (qOf P) e z i)
      change ρ.symm (ρ (h v)) ∈ _ at this
      rwa [ρ.symm_apply_apply] at this
    have h3 : h v (Fin.natAdd n i) = (qOf P : E) ^ e i := by
      rw [← atN_natAdd (h v) i, ← atN_of_R1cond hρ.1 hU, hrv, atN_natAdd, nfGen_natAdd, if_pos rfl]
    have h4 : IntAt P ((qOf P : E) ^ j * h v (Fin.natAdd n i)) := h2 v hv (Fin.natAdd n i)
    rw [h3, ← zpow_natCast, ← zpow_add₀ hq] at h4
    have := nonneg_of_intAt_zpow h4
    omega
  · have hc : 1 ≤ c := by have := i.2; omega
    obtain ⟨u, hu, h'⟩ := (coords_of_mem hc (hmem _ (intV_eN P (n + c) (n + i.1)))).1 i
    refine le_of_zpow_eq hu ?_
    rw [← h', ← atN_natAdd (ρ _) i, atN_of_R1cond hρ.1 (eN_mem_Ufl (by omega)), atN_natAdd]
    simp [Loc.eN]
  · have h3 := (coords_of_mem hc (hmem _ (intV_eN P (n + c) n))).2 a
    have h4 : Loc.eN E (n + c) n (Fin.castAdd c a) = 0 := by
      unfold Loc.eN
      rw [if_neg (by have := a.2; simp; omega)]
    have h5 : Loc.eN E (n + c) n (Fin.natAdd n ⟨0, hc⟩) = 1 := by simp [Loc.eN]
    rw [hρ.1.2.1, h4, h5, one_mul, zero_sub] at h3
    simpa using IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg h3

theorem nfLat_of_eq_zero (P : HeightOneSpectrum (𝓞 E)) (hc : c = 0) (e : Fin c → ℤ) (z z' : Fin n → E) :
    nfLat P n c e z = nfLat P n c e z' := by
  subst hc
  simp [nfLat]

end General

theorem nf_of_between : ∀ (X : Fields) (Pr : Primes X) (R : Ranks) (j : ℕ) (P : HeightOneSpectrum (𝓞 X.E)), P ∉ Pr.vGs → ∀ (h ρ : AutY X R j) (e : Fin (cOf R j) → ℤ) (z : Sp X.E (R.N j)), ρ ∈ Loc.R1 X.E (R.N j) (cOf R j) → Between j P h → (ρ * h) '' {v | IntV P v} = GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.nfLat P (R.N j) (cOf R j) e z → GlobalTheory.IndefiniteRowSideFullHecke.SandwichNormalForm.NF Pr j P (ρ * h) := by
  intro X Pr R j P hP h ρ e z hρ hb hL
  obtain ⟨he, hz⟩ := read_bounds P j h ρ e z hρ hb.1 hb.2 hL
  rcases Nat.eq_zero_or_pos (cOf R j) with hc | hc
  · exact ⟨e, 0, he, zero_mem _, by rw [lamYat_coe hP, hL, nfLat_of_eq_zero P hc e z 0]⟩
  · exact ⟨e, z, he, (mem_stdAt_iff _).2 (hz hc), by rw [lamYat_coe hP, hL]⟩

end GlobalTheory.Proof.hasLatticeNormalForm_of_between

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsRayFieldInRestrictScalars
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.L2.Host GlobalTheory.NT GlobalTheory.Published GlobalTheory.Mem GlobalTheory.Mem.Fld
open scoped nonZeroDivisors IntermediateField

namespace GlobalTheory.Mem.Fld

theorem IsRayField.isRayFieldIn_restrictScalars {K : IntermediateField ℚ ℂ} [NumberField K]
    {M : IntermediateField K ℂ} [hM : NumberField M] {𝔮 : Ideal (𝓞 K)} (h : IsRayField K M 𝔮) :
    IsRayFieldIn (K.val : K →+* ℂ) 𝔮 (M.restrictScalars ℚ) := by
  have hmem : ∀ x : K, (K.val : K →+* ℂ) x ∈ M.restrictScalars ℚ := fun x => by
    rw [IntermediateField.mem_restrictScalars]
    exact M.algebraMap_mem x
  have : NumberField (M.restrictScalars ℚ) := hM
  refine ⟨hmem, inferInstance, ?_⟩
  letI := algOf (K.val : K →+* ℂ) (M.restrictScalars ℚ) hmem
  exact h.of_algEquiv
    { toFun := fun y => ⟨y.1, y.2⟩
      invFun := fun y => ⟨y.1, y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_mul' := fun _ _ => rfl
      map_add' := fun _ _ => rfl
      commutes' := fun _ => rfl }

theorem adjoin_weberSet_one (K : Type) [Field K] [CharZero K] [Algebra K ℂ] (L : PeriodPair) :
    IntermediateField.adjoin K (FieldSize.weberSet L 1) = K⟮(latticeCurve L).j⟯ := by
  have hset : FieldSize.weberSet L 1 = {L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)} := by
    ext w
    simp only [FieldSize.weberSet, Nat.cast_one, div_one, Set.mem_insert_iff, Set.mem_ofPred_eq,
      Set.mem_singleton_iff]
    constructor
    · rintro (hw | ⟨z, hz, hz', -⟩)
      · exact hw
      · exact absurd hz hz'
    · exact fun hw => Or.inl hw
  have hΔ0 : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 := by
    rw [← latticeCurve_Δ L]; exact latticeCurve_Δ_ne_zero L
  have hj : (latticeCurve L).j = 1728 * (L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)) := by
    rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', latticeCurve_c₄,
      latticeCurve_Δ]
    field_simp
    ring
  have h1728 : ∀ S : IntermediateField K ℂ, (1728 : ℂ) ∈ S := fun S => by
    simp
  rw [hset, hj]
  set w := L.g₂ ^ 3 / (L.g₂ ^ 3 - 27 * L.g₃ ^ 2)
  apply le_antisymm
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    have hw : (1728 : ℂ)⁻¹ * (1728 * w) = w := by field_simp
    have hm : (1728 : ℂ)⁻¹ * (1728 * w) ∈ K⟮1728 * w⟯ :=
      mul_mem (inv_mem (h1728 _)) (IntermediateField.mem_adjoin_simple_self K _)
    rwa [hw] at hm
  · rw [IntermediateField.adjoin_le_iff, Set.singleton_subset_iff, SetLike.mem_coe]
    exact mul_mem (h1728 _) (IntermediateField.mem_adjoin_simple_self K _)

theorem isRayFieldIn_hilbertField : WeberRayFieldSt → ∀ (d : ℕ) (F : IntermediateField ℚ ℂ) (A : WeierstrassCurve F),
    d.Prime → d % 4 = 3 → 3 < d → IsGoodCMCurve d F A → ∃ _ : NumberField ℚ⟮sqrtNegNat d⟯,
      discr ℚ⟮sqrtNegNat d⟯ = -(d : ℤ) ∧ Module.finrank ℚ ℚ⟮sqrtNegNat d⟯ = 2 ∧
        IsRayFieldIn (ℚ⟮sqrtNegNat d⟯.val : ℚ⟮sqrtNegNat d⟯ →+* ℂ) ⊤ (hilbertField d F) := by
  intro hW d F A hd h4 h3 hG
  set x := sqrtNegNat d with hxdef
  have hx : x ^ 2 = -(d : ℂ) := sqrtNegNat_sq d
  have hint : IsIntegral ℚ x := by
    refine ⟨Polynomial.X ^ 2 + Polynomial.C (d : ℚ), Polynomial.monic_X_pow_add_C _ two_ne_zero, ?_⟩
    simp [hx]
  have : FiniteDimensional ℚ ℚ⟮x⟯ := IntermediateField.adjoin.finiteDimensional hint
  have hNF : NumberField ℚ⟮x⟯ := NumberField.mk
  obtain ⟨-, hfin, habs⟩ := isGalois_finrank_discr_adjoin_sqrt_neg_prime d x hd h4 hx
  have hd0 : 0 < d := hd.pos
  have hTC : IsTotallyComplex ℚ⟮x⟯ :=
    isTotallyComplex_of_sq_eq_neg hd0 (x := IntermediateField.AdjoinSimple.gen ℚ x)
      (Subtype.ext (by simpa using hx))
  have hdisc : discr ℚ⟮x⟯ = -(d : ℤ) := by
    have hnc : NumberField.InfinitePlace.nrComplexPlaces ℚ⟮x⟯ = 1 := by
      have := IsTotallyComplex.finrank (K := ℚ⟮x⟯)
      omega
    have hs := sign_discr (K := ℚ⟮x⟯)
    rw [hnc, pow_one] at hs
    have hneg : discr ℚ⟮x⟯ < 0 := Int.sign_eq_neg_one_iff_neg.1 hs
    have h := Int.natAbs_eq (discr ℚ⟮x⟯)
    rw [habs] at h
    omega
  have hG' := hG
  obtain ⟨-, -, L, hL, -, -, -⟩ := hG
  have hlat : ∀ z, z ∈ L.lattice ↔ ∃ a : 𝓞 ℚ⟮x⟯, algebraMap ℚ⟮x⟯ ℂ (a : ℚ⟮x⟯) = z := by
    intro z
    rw [hL z]
    constructor
    · rintro ⟨hz, hzi⟩
      have hi : IsIntegral ℤ (⟨z, hz⟩ : ℚ⟮x⟯) :=
        (isIntegral_algHom_iff ((ℚ⟮x⟯).val.toRingHom.toIntAlgHom) Subtype.val_injective).1 hzi
      exact ⟨⟨⟨z, hz⟩, hi⟩, rfl⟩
    · rintro ⟨a, rfl⟩
      exact ⟨(a : ℚ⟮x⟯).2,
        (RingOfIntegers.isIntegral_coe a).map ((ℚ⟮x⟯).val.toRingHom.toIntAlgHom)⟩
  have hdlt : discr ℚ⟮x⟯ < -4 := by rw [hdisc]; omega
  obtain ⟨_, hAb, hRay⟩ := hW ℚ⟮x⟯ hfin hdlt L hlat 1 one_pos
  have hone : Ideal.span {((1 : ℕ) : 𝓞 ℚ⟮x⟯)} = ⊤ := by simp
  rw [hone] at hRay
  have hRF : IsRayField ℚ⟮x⟯ (IntermediateField.adjoin ℚ⟮x⟯ (FieldSize.weberSet L 1)) ⊤ := ⟨hAb, hRay⟩
  refine ⟨hNF, hdisc, hfin, ?_⟩
  have hIn := hRF.isRayFieldIn_restrictScalars
  rw [adjoin_weberSet_one] at hIn
  have hEq : (ℚ⟮x⟯⟮(latticeCurve L).j⟯).restrictScalars ℚ = hilbertField d F := by
    rw [hilbertField_eq hG' hL]
    exact IntermediateField.adjoin_simple_adjoin_simple ℚ (latticeCurve L).j (α := x)
  rw [← hEq]
  exact hIn

end GlobalTheory.Mem.Fld
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSquareAbsNormConjInvariantMovedPrimesIdeal
section
set_option autoImplicit false

namespace GlobalTheory.SquareNorm

open NumberField IsDedekindDomain Formalism.L2.Pj

theorem exists_eq_mul_map {R : Type} [CommRing R] [IsDedekindDomain R] (e : R ≃+* R) (he : ∀ x, e (e x) = x)
    (𝔡 : Ideal R) : 𝔡 ≠ ⊥ → 𝔡.map (e : R →+* R) = 𝔡 →
      (∀ P : Ideal R, P.IsPrime → 𝔡 ≤ P → P.map (e : R →+* R) ≠ P) →
      ∃ 𝔞 : Ideal R, 𝔡 = 𝔞 * 𝔞.map (e : R →+* R) := by
  have hee : ∀ I : Ideal R, (I.map (e : R →+* R)).map (e : R →+* R) = I := fun I => by
    rw [Ideal.map_map]
    have : (e : R →+* R).comp (e : R →+* R) = RingHom.id R := RingHom.ext he
    rw [this, Ideal.map_id]
  induction 𝔡 using WellFoundedGT.induction with
  | ind 𝔡 ih =>
  intro h0 hinv hmv
  by_cases ht : 𝔡 = ⊤
  · exact ⟨⊤, by rw [ht, Ideal.map_top, Ideal.top_mul]⟩
  obtain ⟨P, hP, hle⟩ := Ideal.exists_le_maximal 𝔡 ht
  have hQ : (P.map (e : R →+* R)).IsMaximal := Ideal.IsMaximal.map_bijective (e : R →+* R) e.bijective hP
  have hne := hmv P hP.isPrime hle
  have hle' : 𝔡 ≤ P.map (e : R →+* R) := by
    have := Ideal.map_mono (f := (e : R →+* R)) hle
    rwa [hinv] at this
  have hcop : IsCoprime P (P.map (e : R →+* R)) :=
    Ideal.isCoprime_iff_sup_eq.2 (hP.coprime_of_ne hQ hne.symm)
  obtain ⟨𝔟, hb⟩ := hcop.mul_dvd (Ideal.dvd_iff_le.2 hle) (Ideal.dvd_iff_le.2 hle')
  have hPQ : P * P.map (e : R →+* R) ≠ 0 := fun h => h0 (by rw [hb, h, zero_mul]; rfl)
  have hb0 : 𝔟 ≠ ⊥ := fun h => h0 (by rw [hb, h, Ideal.mul_bot])
  have hdb : 𝔡 ≤ 𝔟 := Ideal.le_of_dvd ⟨P * P.map (e : R →+* R), by rw [mul_comm]; exact hb⟩
  have hlt : 𝔡 < 𝔟 := by
    refine lt_of_le_of_ne hdb fun h => ?_
    have h1 : P * P.map (e : R →+* R) * 𝔟 = 1 * 𝔟 := by rw [← hb, one_mul, h]
    have h2 := mul_right_cancel₀ hb0 h1
    have h3 : (1 : Ideal R) ≤ P := Ideal.le_of_dvd ⟨_, h2.symm⟩
    rw [Ideal.one_eq_top] at h3
    exact hP.ne_top (top_le_iff.1 h3)
  have hbinv : 𝔟.map (e : R →+* R) = 𝔟 := by
    apply mul_left_cancel₀ hPQ
    rw [← hb]
    conv_rhs => rw [← hinv, hb]
    rw [Ideal.map_mul, Ideal.map_mul, hee, mul_comm P]
  obtain ⟨𝔞, ha⟩ := ih 𝔟 hlt hb0 hbinv fun Q hQ' h => hmv Q hQ' (hdb.trans h)
  refine ⟨P * 𝔞, ?_⟩
  rw [hb, Ideal.map_mul]
  conv_lhs => rw [ha]
  ring

theorem isSquare_absNorm : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E) (𝔡 : Ideal (𝓞 E)), 𝔡 ≠ ⊥ → 𝔡.map (H.bar : 𝓞 E →+* 𝓞 E) = 𝔡 → (∀ P : Ideal (𝓞 E), P.IsPrime → 𝔡 ≤ P → P.map (H.bar : 𝓞 E →+* 𝓞 E) ≠ P) → IsSquare (Ideal.absNorm 𝔡) := by
  intro E _ _ _ H 𝔡 h0 hinv hmv
  have he : ∀ x, H.bar (H.bar x) = x := fun x => RingOfIntegers.ext (by
    rw [H.bar_eq, H.bar_eq, IsCMField.complexConj_apply_apply])
  obtain ⟨𝔞, ha⟩ := exists_eq_mul_map H.bar he 𝔡 h0 hinv hmv
  have hN : Ideal.absNorm (𝔞.map (H.bar : 𝓞 E →+* 𝓞 E)) = Ideal.absNorm 𝔞 := by
    rw [Ideal.absNorm_apply, Ideal.absNorm_apply, Submodule.cardQuot_apply, Submodule.cardQuot_apply]
    exact (Nat.card_congr (Ideal.quotientEquiv 𝔞 _ H.bar rfl).toEquiv).symm
  exact ⟨Ideal.absNorm 𝔞, by rw [ha, map_mul, hN]⟩

end GlobalTheory.SquareNorm
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LevelStepZeroAtTwistPrimeFull
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.Col Formalism.L2.DIV GlobalTheory.QNormal GlobalTheory.Mem.Col2.IdxEx

namespace GlobalTheory.Mem.Col2.IdxExZeroQ

section Loc

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)}

theorem parL_self (q kj n c : ℕ) (h : n ≤ kj) : LocE.parL P q kj n c = stdAt E (n + c) P := by
  ext x
  unfold LocE.parL
  rw [GlobalTheory.CongLevel.mem_sclLat, GlobalTheory.GO.ChRoot.mem_stdAt']
  refine forall_congr' fun l => ?_
  rw [if_neg (by omega)]
  simp

theorem lamY_zero (q n c : ℕ) : LocE.lamY P q n c 0 = stdAt E (n + c) P :=
  Submodule.ext fun _ => GlobalTheory.GO.ChRoot.mem_lamY_zero


omit [StarRing E] in
theorem lamQB_empty {K : Type} [Field K] (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (kj n : ℕ) (hn : n ≤ kj) {N : ℕ}
    (h : HomE E N N) : LocE.lamQB ξ kj n h = 1 := by
  unfold LocE.lamQB
  haveI : IsEmpty (Fin (n - kj)) := ⟨fun i => by have := i.2; omega⟩
  have h1 : redP P (1 : E) = 1 := by simpa using reduction_coe P 1
  rw [Matrix.det_isEmpty]
  unfold LocE.unitV
  rw [dite_eq_left (by rw [h1]; exact isUnit_one)]
  have : ∀ hu : IsUnit (redP P (1 : E)), hu.unit = 1 := fun hu => Units.ext (by simp [h1])
  rw [this, map_one]
  simp

end Loc

theorem zero_level : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (P : rowSG Pr sel mu), P.1 ∉ Pr.vGs → cst.Ok → GrpQ (R := R) sel mu cst 0 P 1 ⟨⊤, 1⟩ ∧ ChrQ Ch sel mu cst 0 P 1 ⟨⊤, 1⟩ := by
  intro X Pr R Ch sel S mu cst P hP hc
  have hN : R.N 0 ≤ R.k + 0 := by rw [Ranks.N_zero]; omega
  have hJ : Jat (Pr := Pr) (R := R) cst.sharp 0 P.1 = stabL X.E _ (stdAt X.E (R.N 0 + cOf R 0) P.1) := by
    unfold Jat
    rw [if_neg hP]
    unfold LocE.JQ
    rw [parL_self _ _ _ _ hN, inf_idem]
  have e : ∀ r : AutY X R 0, (MulAut.conj (1 : AutY X R 0)⁻¹).toMonoidHom r = r := by
    intro r
    simp
  constructor
  · unfold GrpQ
    symm
    rw [eq_top_iff]
    intro g _
    rw [Subgroup.mem_subgroupOf]
    refine ⟨GlobalTheory.CongLevel.extE _ g.1, ⟨GlobalTheory.CongLevel.extendByIdOnLastCoordsLinearEquiv_mem_firstRowGroup _ g.1, ?_⟩, GlobalTheory.CongLevel.extE_inX _ g.1⟩
    show (MulAut.conj (1 : AutY X R 0)⁻¹).toMonoidHom (GlobalTheory.CongLevel.extE (cOf R 0) g.1) ∈ Jat (Pr := Pr) cst.sharp 0 P.1
    rw [e, hJ, ← lamY_zero (qOf P.1)]
    exact GlobalTheory.CongLevel.extE_stab _ _ _ _ _ g.2
  · intro g r hr _
    have h2 : (MulAut.conj (1 : AutY X R 0)⁻¹).toMonoidHom r ∈ Jat (Pr := Pr) cst.sharp 0 P.1 := hr.2
    rw [e, hJ] at h2
    have hint : IntAt P.1 (1 * Loc.n1Arg r) :=
      GlobalTheory.GO.ChRoot.intAt_n1Arg 1 r fun x hx => by rw [one_smul]; exact (h2 x).2 hx
    rw [one_mul] at hint
    unfold chiInv lamRow
    rw [if_neg hP, hc.psi_int P _ hint, lamQB_empty _ _ _ hN]
    simp

end GlobalTheory.Mem.Col2.IdxExZeroQ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MainProof
section
open MvPolynomial

noncomputable section

namespace GlobalTheory.WeylLatDualProof

theorem mainProof : WeylLatticeDuality.Stmt := by
  intro p _ Lt T _ _ e he N nu ν hrow hzero φ
  classical
  have hY : ∀ s, (nu s).colLen 0 ≤ N := fun s => colLen_le_of_rowLen (hzero s N le_rfl)
  have hν : ∀ s, ν (e s) = fun r : Fin N => (nu s).rowLen r := fun s => funext fun r => (hrow s r).symm
  choose ι hι hdec b g c d Nc hNc h1 h2 h3 h4 h5 using fun s => _root_.GlobalTheory.WeylLatDualProof.dual_bases_colProd GlobalTheory.T.columnMinorProducts_fock_reproducing_identity N (nu s) (hY s)
  rw [_root_.GlobalTheory.WeylLatDualProof.integral_minors_iff_basis p Lt N nu hY ι b c d h1 h2 φ]
  have hfun : (fun y : T → Matrix (Fin N) (Fin N) ℂ_[p] =>
      φ (WeylLatticeDuality.DeX N nu fun s => WeylLatticeDuality.colsOf (y (e s)))) = fun y =>
        ∑ κ : (∀ s, ι s), φ (MvPolynomial.map (algebraMap ℚ ℂ_[p])
            (∏ s, MvPolynomial.rename (sig N s) (b s (κ s)))) *
          ∏ s, MvPolynomial.eval (fun k : Fin N × Fin N => y (e s) k.1 k.2)
            (MvPolynomial.map (algebraMap ℚ ℂ_[p]) (g s (κ s))) :=
    funext fun y => _root_.GlobalTheory.WeylLatDualProof.phi_DeX_expand p Lt T e N nu hY ι b g c h1 h3 φ y
  rw [hfun, _root_.GlobalTheory.WeylCombInt.comb_mem_iff p Lt T e he N ν ι b g Nc hNc h4 (fun s => by rw [hν s]; exact h5 s)]

end GlobalTheory.WeylLatDualProof
end
end

