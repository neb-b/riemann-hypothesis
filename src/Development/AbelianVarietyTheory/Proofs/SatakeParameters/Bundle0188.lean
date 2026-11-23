module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFiniteClass
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
public import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WeilDeligneParamMonodromyEqZeroIff
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitExEveryDatum

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.DoubleCosetOperatorTranslateDeeperLevelEqSmul
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.HeckeAverage


open Classical in
theorem finsum_translate_eq {G : Type} [Group G] (J J' : Subgroup G) (h : G)
    (hconj : ∀ κ ∈ J', h⁻¹ * κ * h ∈ J)
    (hfin : {c : G ⧸ J' | ∃ x ∈ (J : Set G), (x : G ⧸ J') = c}.Finite) :
    ∃ m : ℕ, 0 < m ∧ ∀ (W : Type) [AddCommGroup W] (f : G → W), (∀ κ ∈ J, ∀ g, f (g * κ) = f g) → ∀ g : G,
      (∑ᶠ c : G ⧸ J', if hc : ∃ x ∈ (J : Set G), (x : G ⧸ J') = c then f (g * hc.choose * h) else 0) =
      m • ∑ᶠ d : G ⧸ J, if hd : ∃ x ∈ {x | ∃ u ∈ J, ∃ u' ∈ J, x = u * h * u'}, (x : G ⧸ J) = d
        then f (g * hd.choose) else 0 := by
  let φ : G ⧸ J' → G ⧸ J := fun c => ((c.out * h : G) : G ⧸ J)
  have hφ : ∀ x : G, φ (x : G ⧸ J') = ((x * h : G) : G ⧸ J) := by
    intro x
    have h1 : ((x : G ⧸ J').out)⁻¹ * x ∈ J' := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    refine QuotientGroup.eq.2 ?_
    have := hconj _ h1
    convert this using 1
    group
  have hφs : ∀ (u : G) (c : G ⧸ J'), φ (u • c) = u • φ c := by
    intro u c
    induction c using QuotientGroup.induction_on with
    | H x =>
      rw [MulAction.Quotient.smul_mk, hφ, hφ, MulAction.Quotient.smul_mk]
      simp [mul_assoc]
  let S : Finset (G ⧸ J') := hfin.toFinset
  have hS : ∀ c, c ∈ S ↔ ∃ x ∈ (J : Set G), (x : G ⧸ J') = c := fun c => hfin.mem_toFinset
  have hSs : ∀ u ∈ J, ∀ c ∈ S, u • c ∈ S := by
    intro u hu c hc
    obtain ⟨x, hx, rfl⟩ := (hS c).1 hc
    exact (hS _).2 ⟨u * x, J.mul_mem hu hx, rfl⟩
  have hT : ∀ d, d ∈ S.image φ ↔ ∃ x ∈ {x | ∃ u ∈ J, ∃ u' ∈ J, x = u * h * u'}, (x : G ⧸ J) = d := by
    intro d
    rw [Finset.mem_image]
    constructor
    · rintro ⟨c, hc, rfl⟩
      obtain ⟨x, hx, rfl⟩ := (hS c).1 hc
      exact ⟨x * h, ⟨x, hx, 1, J.one_mem, by simp⟩, (hφ x).symm⟩
    · rintro ⟨_, ⟨u, hu, u', hu', rfl⟩, rfl⟩
      refine ⟨(u : G ⧸ J'), (hS _).2 ⟨u, hu, rfl⟩, ?_⟩
      rw [hφ]
      exact QuotientGroup.eq.2 (by simpa [mul_assoc] using hu')
  have hcard : ∀ d ∈ S.image φ, (S.filter (fun c => φ c = d)).card =
      (S.filter (fun c => φ c = (h : G ⧸ J))).card := by
    intro d hd
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hd
    obtain ⟨u, hu, rfl⟩ := (hS c).1 hc
    have e : φ (u : G ⧸ J') = u • (h : G ⧸ J) := by rw [hφ]; rfl
    symm
    refine Finset.card_nbij' (fun c => u • c) (fun c => u⁻¹ • c) ?_ ?_ ?_ ?_
    · intro c hc
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hc ⊢
      exact ⟨hSs u hu c hc.1, by rw [hφs, hc.2, e]⟩
    · intro c hc
      simp only [Finset.coe_filter, Set.mem_setOf_eq] at hc ⊢
      exact ⟨hSs u⁻¹ (J.inv_mem hu) c hc.1, by rw [hφs, hc.2, e, inv_smul_smul]⟩
    · intro c _
      simp
    · intro c _
      simp
  refine ⟨(S.filter (fun c => φ c = (h : G ⧸ J))).card, ?_, ?_⟩
  · refine Finset.card_pos.2 ⟨((1 : G) : G ⧸ J'), Finset.mem_filter.2 ⟨(hS _).2 ⟨1, J.one_mem, rfl⟩, ?_⟩⟩
    rw [hφ, one_mul]
  intro W _ f hf g
  let F : G ⧸ J → W := fun d => f (g * d.out)
  have hF : ∀ y : G, F (y : G ⧸ J) = f (g * y) := by
    intro y
    have h1 : ((y : G ⧸ J).out)⁻¹ * y ∈ J := QuotientGroup.eq.1 (QuotientGroup.out_eq' _)
    have := hf _ h1 (g * (y : G ⧸ J).out)
    show f (g * (y : G ⧸ J).out) = _
    rw [← this]
    congr 1
    group
  rw [finsum_eq_sum_of_support_subset (s := S), finsum_eq_sum_of_support_subset (s := S.image φ)]
  · have e1 : (∑ c ∈ S, if hc : ∃ x ∈ (J : Set G), (x : G ⧸ J') = c then f (g * hc.choose * h) else 0) =
        ∑ c ∈ S, F (φ c) := by
      refine Finset.sum_congr rfl fun c hc => ?_
      have hc' := (hS c).1 hc
      rw [dite_eq_left hc']
      conv_rhs => rw [← hc'.choose_spec.2, hφ, hF]
      rw [mul_assoc]
    have e2 : (∑ d ∈ S.image φ, if hd : ∃ x ∈ {x | ∃ u ∈ J, ∃ u' ∈ J, x = u * h * u'}, (x : G ⧸ J) = d
        then f (g * hd.choose) else 0) = ∑ d ∈ S.image φ, F d := by
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd' := (hT d).1 hd
      rw [dite_eq_left hd']
      conv_rhs => rw [← hd'.choose_spec.2, hF]
    rw [e1, e2, Finset.sum_comp F φ, Finset.smul_sum]
    refine Finset.sum_congr rfl fun d hd => ?_
    rw [← hcard d hd]
  · intro d hd
    by_contra hn
    exact hd (dif_neg fun h' => hn (Finset.mem_coe.2 ((hT d).2 h')))
  · intro c hc
    by_contra hn
    exact hc (dif_neg fun h' => hn (Finset.mem_coe.2 ((hS c).2 h')))

theorem heckeD_rt_eq_smul : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (J J' : Subgroup (GAf L n)) (h : GAf L n), J' ≤ J → (∀ κ ∈ J', h⁻¹ * κ * h ∈ J) → {c : GAf L n ⧸ J' | ∃ x ∈ (J : Set (GAf L n)), (x : GAf L n ⧸ J') = c}.Finite → ∃ m : ℕ, 0 < m ∧ ∀ (W : Type) [AddCommGroup W] [Module ℂ W] (f : GAf L n → W), (∀ κ ∈ J, NG.rt L n κ f = f) → NG.heckeD J' (J : Set (GAf L n)) (NG.rt L n h f) = (m : ℂ) • NG.heckeD J {x | ∃ u ∈ J, ∃ u' ∈ J, x = u * h * u'} f := by
  intro L _ _ _ n J J' h _ hconj hfin
  obtain ⟨m, hm, H⟩ := finsum_translate_eq J J' h hconj hfin
  refine ⟨m, hm, fun W _ _ f hf => ?_⟩
  funext g
  have := H W f (fun κ hκ g => congrFun (hf κ hκ) g) g
  rw [Pi.smul_apply, Nat.cast_smul_eq_nsmul]
  exact this

end GlobalTheory.HeckeAverage
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqAlgebraMapOfCharpoly
section
noncomputable section

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial Module IsNilpotent

namespace GlobalTheory.WeilDeligne.InertiaSplit

variable {l : ℕ} [Fact l.Prime]

theorem toEndC_coord (ι : Qbar l ≃+* ℂ) {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n (Qbar l)) (v : n → Qbar l) :
    toEndC ι M (fun k => ι (v k)) = fun i => ι ((M.mulVec v) i) := by
  funext i
  rw [toEndC_apply, Matrix.toLin'_apply]
  exact (RingHom.map_mulVec ι.toRingHom M v i).symm

theorem mem_of_exp (ι : Qbar l ≃+* ℂ) {n : Type} [Fintype n] [DecidableEq n]
    (S : Submodule ℂ (n → ℂ)) {M : Matrix n n (Qbar l)} (hM : IsNilpotent M)
    (hS : ∀ v ∈ S, toEndC ι M v ∈ S) : ∀ v ∈ S, toEndC ι (exp M) v ∈ S := by
  obtain ⟨k, hk⟩ := hM
  intro v hv
  set_option synthInstance.maxHeartbeats 100000 in
    rw [exp_eq_sum hk, map_sum, LinearMap.sum_apply]
  refine S.sum_mem fun i hi => ?_
  clear hi
  rw [map_rat_smul, LinearMap.smul_apply, map_pow]
  refine S.smul_of_tower_mem _ ?_
  induction i with
  | zero => simpa using hv
  | succ i ih => rw [pow_succ', mul_apply_eq_comp]; exact hS _ ih

theorem exp_apply_of_eq_zero (ι : Qbar l ≃+* ℂ) {n : Type} [Fintype n] [DecidableEq n]
    {M : Matrix n n (Qbar l)} (hM : IsNilpotent M) {v : n → ℂ} (hv : toEndC ι M v = 0) :
    toEndC ι (exp M) v = v := by
  obtain ⟨k, hk⟩ := hM
  set_option synthInstance.maxHeartbeats 100000 in
    rw [exp_eq_sum (k := k + 1) (pow_eq_zero_of_le (Nat.le_succ k) hk), Finset.sum_range_succ', map_add (f := _),
    map_sum, LinearMap.add_apply, LinearMap.sum_apply, Finset.sum_eq_zero]
  · simp
  · intro i _
    rw [map_rat_smul, LinearMap.smul_apply, map_pow, _root_.pow_succ, mul_apply_eq_comp, hv, map_zero,
      smul_zero]

theorem eq_algebraMap_of_charpoly {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    {x : Module.End ℂ V} (hs : x.IsSemisimple) {z : ℂ}
    (hc : x.charpoly = (X - C z) ^ finrank ℂ V) : x = algebraMap ℂ (Module.End ℂ V) z := by
  have h0 := LinearMap.aeval_self_charpoly x
  rw [hc, map_pow, map_sub, aeval_X, aeval_C] at h0
  have hs' : (x - algebraMap ℂ (Module.End ℂ V) z).IsSemisimple :=
    Module.End.isSemisimple_sub_algebraMap_iff.2 hs
  exact sub_eq_zero.1 (Module.End.eq_zero_of_isNilpotent_isSemisimple ⟨_, h0⟩ hs')

def pull (ι : Qbar l ≃+* ℂ) {a n m : ℕ} (f : (Fin a → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) × (Fin m → ℂ)) :
    (Fin a → Qbar l) ≃ₗ[Qbar l] (Fin n → Qbar l) × (Fin m → Qbar l) where
  toFun v := (fun j => ι.symm ((f (fun k => ι (v k))).1 j), fun j => ι.symm ((f (fun k => ι (v k))).2 j))
  invFun y := fun k => ι.symm (f.symm (fun j => ι (y.1 j), fun j => ι (y.2 j)) k)
  map_add' v v' := by
    have e : (fun k => ι ((v + v') k)) = (fun k => ι (v k)) + fun k => ι (v' k) := by
      funext k; simp
    simp only [e, map_add (f := _)]
    ext j <;> simp
  map_smul' c v := by
    have e : (fun k => ι ((c • v) k)) = ι c • fun k => ι (v k) := by funext k; simp
    simp only [e, map_smul]
    ext j <;> simp
  left_inv v := by
    funext k; simp
  right_inv y := by
    ext j <;> simp

theorem pull_apply (ι : Qbar l ≃+* ℂ) {a n m : ℕ} (f : (Fin a → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) × (Fin m → ℂ))
    (v : Fin a → Qbar l) :
    pull ι f v = (fun j => ι.symm ((f (fun k => ι (v k))).1 j),
      fun j => ι.symm ((f (fun k => ι (v k))).2 j)) := rfl

theorem pull_fst_eq_zero (ι : Qbar l ≃+* ℂ) {a n m : ℕ} (f : (Fin a → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) × (Fin m → ℂ))
    (v : Fin a → Qbar l) : (pull ι f v).1 = 0 ↔ (f (fun k => ι (v k))).1 = 0 := by
  rw [pull_apply]
  constructor
  · intro e; funext j; simpa using congrFun e j
  · intro e; funext j; simp [e]

theorem pull_snd_eq_zero (ι : Qbar l ≃+* ℂ) {a n m : ℕ} (f : (Fin a → ℂ) ≃ₗ[ℂ] (Fin n → ℂ) × (Fin m → ℂ))
    (v : Fin a → Qbar l) : (pull ι f v).2 = 0 ↔ (f (fun k => ι (v k))).2 = 0 := by
  rw [pull_apply]
  constructor
  · intro e; funext j; simpa using congrFun e j
  · intro e; funext j; simp [e]

end GlobalTheory.WeilDeligne.InertiaSplit

namespace GlobalTheory.WeilDeligne.InertiaSplit

variable {l : ℕ} [Fact l.Prime]
variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
variable {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver A w}

theorem split_away (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) (ι : Qbar l ≃+* ℂ) {a : ℕ}
    (r : G E Ω →* GL (Fin a) (Qbar l))
    (hr : Continuous fun g => ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)))
    (x y : WD h) (hxy : wdOf (h := h) hl ι r = x.lpSum y) :
    ∃ U U' : Submodule (Qbar l) (Fin a → Qbar l), IsCompl U U' ∧ finrank (Qbar l) U = x.lpDim ∧
      finrank (Qbar l) U' = y.lpDim ∧
      (∀ σ ∈ Ine (F := E) A,
        (∀ v ∈ U, ((r σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).mulVec v ∈ U) ∧
        (∀ v ∈ U', ((r σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).mulVec v ∈ U')) ∧
      (y.mono0 → ∀ σ ∈ Ine (F := E) A, ∀ c : Qbar l, y.inePol σ = (X - C (ι c)) ^ y.lpDim →
        ∀ v ∈ U', ((r σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).mulVec v = c • v) := by
  induction x using WD.ind with | hP n b => ?_
  induction y using WD.ind with | hP m c => ?_
  have ht := isTameChar_tameL h hl
  obtain ⟨N, hN⟩ := exists_isMonodromy h hl ht hr
  obtain ⟨z, hz⟩ := IsMonodromy.exists_isFrobSS hl ht hN (deg_frob (h := h)) ι
  have e : wdOf (h := h) hl ι r = WD.mk z := by
    have hz' : IsWDOf ι r (WD.mk z) := ⟨_, ht, _, deg_frob, N, z, hN, hz, rfl⟩
    have hex : ∃ x : WD h, IsWDOf ι r x := ⟨WD.mk z, hz'⟩
    rw [wdOf, dite_eq_left hex]
    exact IsWDOf.unique hl hex.choose_spec hz'
  rw [e, WD.lpSum_mk, WD.mk_eq_mk] at hxy
  obtain ⟨f, hfρ, hfN⟩ := hxy

  have hin : ∀ σ (hσ : σ ∈ Ine (F := E) A) (u : Fin a → ℂ),
      toEndC ι ((r σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) u =
        z.ρ (ineIncl h ⟨σ, hσ⟩) (toEndC ι (exp (tval (tameL h hl) ⟨σ, hσ⟩ • N)) u) := by
    intro σ hσ u
    have hm : ((r σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)) =
        wdMat (tameL h hl) (deg_frob (h := h)) r N (ineIncl h ⟨σ, hσ⟩) *
          exp (tval (tameL h hl) ⟨σ, hσ⟩ • N) := by
      rw [wdMat_ineIncl, mul_assoc, ← exp_add_smul hN.1, neg_add_cancel, zero_smul,
        IsNilpotent.exp_zero, mul_one]
    rw [hm, map_mul, mul_apply_eq_comp, ← hN.rep_apply hl ht deg_frob ι,
      ← hz.ρ_ineIncl (hN.isSmooth_rep hl ht deg_frob ι)]

  have stρ2 : ∀ g u, (f u).2 = 0 → (f (z.ρ g u)).2 = 0 := fun g u hu => by
    rw [hfρ]; simp [hu]
  have stρ1 : ∀ g u, (f u).1 = 0 → (f (z.ρ g u)).1 = 0 := fun g u hu => by
    rw [hfρ]; simp [hu]
  have stN2 : ∀ u, (f u).2 = 0 → (f (z.N u)).2 = 0 := fun u hu => by
    rw [hfN]; simp [hu]
  have stN1 : ∀ u, (f u).1 = 0 → (f (z.N u)).1 = 0 := fun u hu => by
    rw [hfN]; simp [hu]
  have ste2 : ∀ (s : Qbar l) u, (f u).2 = 0 → (f (toEndC ι (exp (s • N)) u)).2 = 0 := by
    intro s u hu
    have := mem_of_exp ι (LinearMap.ker ((LinearMap.snd ℂ (Fin n → ℂ) (Fin m → ℂ)).comp
      (f : (Fin a → ℂ) →ₗ[ℂ] (Fin n → ℂ) × (Fin m → ℂ)))) (hN.1.smul s) (fun v hv => by
        simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.snd_apply,
          LinearEquiv.coe_coe] at hv ⊢
        rw [toEndC_smul, LinearMap.smul_apply, ← hz.1, map_smul, Prod.smul_snd, stN2 v hv, smul_zero])
      u (by simpa using hu)
    simpa using this
  have ste1 : ∀ (s : Qbar l) u, (f u).1 = 0 → (f (toEndC ι (exp (s • N)) u)).1 = 0 := by
    intro s u hu
    have := mem_of_exp ι (LinearMap.ker ((LinearMap.fst ℂ (Fin n → ℂ) (Fin m → ℂ)).comp
      (f : (Fin a → ℂ) →ₗ[ℂ] (Fin n → ℂ) × (Fin m → ℂ)))) (hN.1.smul s) (fun v hv => by
        simp only [LinearMap.mem_ker, LinearMap.coe_comp, Function.comp_apply, LinearMap.fst_apply,
          LinearEquiv.coe_coe] at hv ⊢
        rw [toEndC_smul, LinearMap.smul_apply, ← hz.1, map_smul, Prod.smul_fst, stN1 v hv, smul_zero])
      u (by simpa using hu)
    simpa using this

  have hC : IsCompl (LinearMap.ker (LinearMap.snd (Qbar l) (Fin n → Qbar l) (Fin m → Qbar l)))
      (LinearMap.ker (LinearMap.fst (Qbar l) (Fin n → Qbar l) (Fin m → Qbar l))) := by
    rw [← LinearMap.range_inl, ← LinearMap.range_inr]
    exact LinearMap.isCompl_range_inl_inr
  have hC' := (Submodule.orderIsoMapComap (pull ι f).symm).isCompl hC
  simp only [Submodule.orderIsoMapComap_apply] at hC'
  have memU : ∀ v : Fin a → Qbar l, v ∈ (LinearMap.ker (LinearMap.snd (Qbar l) (Fin n → Qbar l) (Fin m → Qbar l))).map
      ((pull ι f).symm : (Fin n → Qbar l) × (Fin m → Qbar l) →ₗ[Qbar l] (Fin a → Qbar l)) ↔ (f (fun k => ι (v k))).2 = 0 := fun v => by
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm, LinearMap.mem_ker, LinearMap.snd_apply,
      pull_snd_eq_zero]
  have memU' : ∀ v : Fin a → Qbar l, v ∈ (LinearMap.ker (LinearMap.fst (Qbar l) (Fin n → Qbar l) (Fin m → Qbar l))).map
      ((pull ι f).symm : (Fin n → Qbar l) × (Fin m → Qbar l) →ₗ[Qbar l] (Fin a → Qbar l)) ↔ (f (fun k => ι (v k))).1 = 0 := fun v => by
    rw [Submodule.mem_map_equiv, LinearEquiv.symm_symm, LinearMap.mem_ker, LinearMap.fst_apply,
      pull_fst_eq_zero]
  refine ⟨_, _, hC', ?_, ?_, fun σ hσ => ⟨fun v hv => ?_, fun v hv => ?_⟩, ?_⟩
  · rw [WD.lpDim_mk, Module.finrank_fin_fun, LinearEquiv.finrank_map_eq, ← LinearMap.range_inl,
      LinearMap.finrank_range_of_inj LinearMap.inl_injective, Module.finrank_fin_fun]
  · rw [WD.lpDim_mk, Module.finrank_fin_fun, LinearEquiv.finrank_map_eq, ← LinearMap.range_inr,
      LinearMap.finrank_range_of_inj LinearMap.inr_injective, Module.finrank_fin_fun]
  · rw [memU] at hv ⊢
    rw [← toEndC_coord, hin σ hσ]
    exact stρ2 _ _ (ste2 _ _ hv)
  · rw [memU'] at hv ⊢
    rw [← toEndC_coord, hin σ hσ]
    exact stρ1 _ _ (ste1 _ _ hv)
  · intro hm σ hσ c0 hc v hv
    rw [WD.monodromyZero_ofWeilDeligneRepClass_iff] at hm
    rw [WD.inePol_of_mem_Ine _ hσ, WD.charPol_mk, WD.lpDim_mk] at hc
    have hsc := eq_algebraMap_of_charpoly (c.semisimple _) hc
    rw [memU'] at hv
    set u : Fin a → ℂ := fun k => ι (v k) with hu
    have hNu : z.N u = 0 := by
      rw [← f.map_eq_zero_iff, hfN]
      ext j <;> simp [hv, hm]
    suffices H : (fun i => ι ((((r σ : GL _ _) : Matrix (Fin a) (Fin a) (Qbar l)).mulVec v) i)) =
        fun i => ι ((c0 • v) i) by
      funext i; exact ι.injective (congrFun H i)
    have hcu : (fun i => ι ((c0 • v) i)) = ι c0 • u := by funext i; simp [hu]
    rw [← toEndC_coord, hin σ hσ, exp_apply_of_eq_zero ι (hN.1.smul _)
      (by rw [toEndC_smul, LinearMap.smul_apply, ← hz.1, hNu, smul_zero]), hcu]
    apply f.injective
    rw [hfρ, map_smul]
    refine Prod.ext ?_ ?_
    · rw [WDRep.sum_ρ, LinearMap.prodMap_apply, Prod.smul_fst, hv, map_zero, smul_zero]
    · rw [WDRep.sum_ρ, LinearMap.prodMap_apply, Prod.smul_snd, hsc, Module.algebraMap_end_apply]

end GlobalTheory.WeilDeligne.InertiaSplit

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOrIsConjPlaceOfOverSplitPlace
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.SplitPlaceOver

theorem host_conj_eq' (D : D7) (x : D.host.E) : D.host.conj x = IsCMField.complexConj D.host.E x :=
  D.host.φ₀.injective (by
    rw [NumberField.IsCMField.complexEmbedding_complexConj, Formalism.HC.HostAx.conjE_apply])

theorem eq_or_isConjPl : ∀ (D : D7) (s : SplitPlace D.host.E) (w : PlE D.host), NG.OverPl w s.v →
    s.w = w ∨ IsConjPl D.host w s.w := by
  intro D s w hov
  let cO := IsCMField.ringOfIntegersComplexConj D.host.E
  have cc (x : 𝓞 D.host.E) : cO (cO x) = x := by
    apply RingOfIntegers.ext
    rw [IsCMField.coe_ringOfIntegersComplexConj, IsCMField.coe_ringOfIntegersComplexConj]
    exact IsCMField.complexConj_apply_apply D.host.E (x : D.host.E)
  let Q : PlE D.host := {
    asIdeal := s.w.asIdeal.comap (cO : 𝓞 D.host.E →+* 𝓞 D.host.E)
    isPrime := Ideal.comap_isPrime _ _
    ne_bot := by
      obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot s.w.ne_bot
      refine (Submodule.ne_bot_iff _).2 ⟨cO y, ?_, ?_⟩
      · show (cO : 𝓞 D.host.E →+* 𝓞 D.host.E) (cO y) ∈ s.w.asIdeal
        rw [RingHom.coe_coe, cc]; exact hy
      · intro h0
        apply hy0
        rw [← cc y, h0, map_zero] }
  have hQ (x : 𝓞 D.host.E) : x ∈ Q.asIdeal ↔ cO x ∈ s.w.asIdeal := Iff.rfl
  have he : w = s.w ∨ w = Q := by
    by_contra hne
    push Not at hne
    obtain ⟨h1, h2⟩ := hne
    have nle : ∀ P : PlE D.host, w ≠ P → ¬ w.asIdeal ≤ P.asIdeal := fun P h hle =>
      h (HeightOneSpectrum.ext (w.isMaximal.eq_of_le P.isPrime.ne_top hle))
    obtain ⟨a, ha, haP⟩ := Set.not_subset.mp (nle s.w h1)
    obtain ⟨b, hb, hbQ⟩ := Set.not_subset.mp (nle Q h2)
    have key : ∃ x ∈ w.asIdeal, x ∉ s.w.asIdeal ∧ x ∉ Q.asIdeal := by
      by_cases haQ : a ∈ Q.asIdeal
      · by_cases hbP : b ∈ s.w.asIdeal
        · refine ⟨a + b, w.asIdeal.add_mem ha hb, fun h => haP ?_, fun h => hbQ ?_⟩
          · simpa using s.w.asIdeal.sub_mem h hbP
          · simpa using Q.asIdeal.sub_mem h haQ
        · exact ⟨b, hb, hbP, hbQ⟩
      · exact ⟨a, ha, haP, haQ⟩
    obtain ⟨x, hx, hxP, hxQ⟩ := key
    rw [hQ] at hxQ
    have hfix : cO (x * cO x) = x * cO x := by rw [map_mul, cc, mul_comm]
    obtain ⟨y, hy⟩ := (IsCMField.ringOfIntegersComplexConj_eq_self_iff D.host.E _).1 hfix
    have hyw : y ∈ w.asIdeal.comap (algebraMap (𝓞 (maximalRealSubfield D.host.E)) (𝓞 D.host.E)) := by
      rw [Ideal.mem_comap, hy]; exact w.asIdeal.mul_mem_right _ hx
    rw [hov.trans s.w_under.symm, Ideal.mem_comap, hy] at hyw
    rcases s.w.isPrime.mem_or_mem hyw with h | h
    · exact hxP h
    · exact hxQ h
  rcases he with e | e
  · exact Or.inl e.symm
  · right
    intro x y hxy
    have hy : y = cO x := by
      apply RingOfIntegers.ext
      rw [hxy, IsCMField.coe_ringOfIntegersComplexConj, host_conj_eq']
    rw [e, hQ, hy]

end GlobalTheory.SplitPlaceOver
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.EquivariantIsoOfTranslationStableGraph
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory

theorem isoRep_of_stable_graph : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) {A B : Type} [AddCommGroup A] [Module ℂ A] [AddCommGroup B] [Module ℂ B] (ρa : Representation ℂ (GQ L n) A) (ρb : Representation ℂ (GQ L n) B) (S₁ : Submodule ℂ (GAf L n → A)) (S₂ : Submodule ℂ (GAf L n → B)) (W : Submodule ℂ ((GAf L n → A) × (GAf L n → B))), NG.IsIrrRep ρa S₁ → NG.IsIrrRep ρb S₂ → (∀ w ∈ W, w.1 ∈ S₁ ∧ w.2 ∈ S₂) → (∀ h, ∀ w ∈ W, (NG.rt L n h w.1, NG.rt L n h w.2) ∈ W) → (∀ u, ((0 : GAf L n → A), u) ∈ W → u = 0) → (∀ u, (u, (0 : GAf L n → B)) ∈ W → u = 0) → W ≠ ⊥ → NG.IsoRep S₁ S₂ := by
  intro L _ _ _ n A B _ _ _ _ ρa ρb S₁ S₂ W h₁ h₂ hW hst h0 h0' hne
  have inj1 : ∀ w ∈ W, w.1 = 0 → w = 0 := by
    intro w hw e
    have : w = (0, w.2) := Prod.ext e rfl
    have h2 := h0 w.2 (this ▸ hw)
    exact Prod.ext e h2
  have inj2 : ∀ w ∈ W, w.2 = 0 → w = 0 := by
    intro w hw e
    have : w = (w.1, 0) := Prod.ext rfl e
    have h2 := h0' w.1 (this ▸ hw)
    exact Prod.ext h2 e
  obtain ⟨w₀, hw₀, hw₀ne⟩ := (Submodule.ne_bot_iff W).1 hne
  have le1 : W.map (LinearMap.fst ℂ _ _) ≤ S₁ := by
    rintro _ ⟨w, hw, rfl⟩; exact (hW w hw).1
  have le2 : W.map (LinearMap.snd ℂ _ _) ≤ S₂ := by
    rintro _ ⟨w, hw, rfl⟩; exact (hW w hw).2
  have e1 : W.map (LinearMap.fst ℂ _ _) = S₁ := by
    refine (h₁.2.2 _ ⟨le1.trans h₁.1.1, ?_⟩ le1).resolve_left ?_
    · rintro h _ ⟨w, hw, rfl⟩
      exact ⟨_, hst h w hw, rfl⟩
    · intro hb
      have : w₀.1 ∈ W.map (LinearMap.fst ℂ _ _) := ⟨w₀, hw₀, rfl⟩
      rw [hb, Submodule.mem_bot] at this
      exact hw₀ne (inj1 w₀ hw₀ this)
  have e2 : W.map (LinearMap.snd ℂ _ _) = S₂ := by
    refine (h₂.2.2 _ ⟨le2.trans h₂.1.1, ?_⟩ le2).resolve_left ?_
    · rintro h _ ⟨w, hw, rfl⟩
      exact ⟨_, hst h w hw, rfl⟩
    · intro hb
      have : w₀.2 ∈ W.map (LinearMap.snd ℂ _ _) := ⟨w₀, hw₀, rfl⟩
      rw [hb, Submodule.mem_bot] at this
      exact hw₀ne (inj2 w₀ hw₀ this)
  let p₁ : W →ₗ[ℂ] S₁ := ((LinearMap.fst ℂ _ _).comp W.subtype).codRestrict S₁ (fun w => (hW w.1 w.2).1)
  let p₂ : W →ₗ[ℂ] S₂ := ((LinearMap.snd ℂ _ _).comp W.subtype).codRestrict S₂ (fun w => (hW w.1 w.2).2)
  have b₁ : Function.Bijective p₁ := by
    refine ⟨(injective_iff_map_eq_zero p₁).2 fun w hw => ?_, fun f => ?_⟩
    · exact Subtype.ext (inj1 w.1 w.2 (congrArg Subtype.val hw))
    · have : f.1 ∈ W.map (LinearMap.fst ℂ _ _) := by rw [e1]; exact f.2
      obtain ⟨w, hw, e⟩ := this
      exact ⟨⟨w, hw⟩, Subtype.ext e⟩
  have b₂ : Function.Bijective p₂ := by
    refine ⟨(injective_iff_map_eq_zero p₂).2 fun w hw => ?_, fun f => ?_⟩
    · exact Subtype.ext (inj2 w.1 w.2 (congrArg Subtype.val hw))
    · have : f.1 ∈ W.map (LinearMap.snd ℂ _ _) := by rw [e2]; exact f.2
      obtain ⟨w, hw, e⟩ := this
      exact ⟨⟨w, hw⟩, Subtype.ext e⟩
  refine ⟨(LinearEquiv.ofBijective p₁ b₁).symm.trans (LinearEquiv.ofBijective p₂ b₂), ?_⟩
  intro h f f' hf
  obtain ⟨w, rfl⟩ := b₁.2 f
  have hf' : f' = p₁ ⟨_, hst h w.1 w.2⟩ := Subtype.ext hf
  subst hf'
  have key : ∀ v : W, ((LinearEquiv.ofBijective p₁ b₁).symm.trans (LinearEquiv.ofBijective p₂ b₂)) (p₁ v) = p₂ v := by
    intro v
    have : (LinearEquiv.ofBijective p₁ b₁).symm (p₁ v) = v :=
      (LinearEquiv.ofBijective p₁ b₁).symm_apply_apply v
    rw [LinearEquiv.trans_apply, this]; rfl
  rw [key, key]
  rfl

end GlobalTheory
end

