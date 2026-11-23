module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.DimZ1fCrystallineDeformation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0034
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0447
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OrdinaryDeformation
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0025
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Bundle0001

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.FinrankLocalCocyclesAdjointUnitaryThreeEqTwelve
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial

private theorem wt_cases (a b : Fin 3) : ∃ j : Fin 5, wt a b = ((j : ℕ) : ℤ) - 2 := by
  revert a b; decide

private theorem sum_dim {E G : Type} [Field E] (S : Submodule E (G → Matrix (Fin 3) (Fin 3) E))
    [Module.Finite E S]
    (h : ∀ j : ℤ, ∀ γ ∈ S, (fun g => Matrix.of fun a b => if wt a b = j then γ g a b else 0) ∈ S) :
    finrank E S = ∑ j : Fin 5,
      finrank E ↥(S ⊓ Submodule.pi Set.univ fun _ => UpperTheory.V.U3.gw E (((j : ℕ) : ℤ) - 2)) := by
  classical
  let T : Fin 5 → Submodule E (G → Matrix (Fin 3) (Fin 3) E) := fun j =>
    S ⊓ Submodule.pi Set.univ fun _ => UpperTheory.V.U3.gw E (((j : ℕ) : ℤ) - 2)
  haveI : ∀ j, Module.Finite E (T j) := fun j => Submodule.finiteDimensional_of_le (inf_le_left : T j ≤ S)
  let f : (∀ j, T j) →ₗ[E] S :=
    { toFun := fun x => ⟨∑ j, (x j : G → Matrix (Fin 3) (Fin 3) E), S.sum_mem fun j _ => (x j).2.1⟩
      map_add' := fun x y => by ext1; simp [Finset.sum_add_distrib]
      map_smul' := fun c x => by ext1; simp [Finset.smul_sum] }
  have hinj : ∀ i j : Fin 5, ((i : ℕ) : ℤ) - 2 = ((j : ℕ) : ℤ) - 2 → i = j := fun i j hij =>
    Fin.ext (by omega)
  have hval : ∀ (x : ∀ j, T j) (g : G) (a b : Fin 3) (j : Fin 5), wt a b = ((j : ℕ) : ℤ) - 2 →
      (f x : G → Matrix (Fin 3) (Fin 3) E) g a b = (x j : G → Matrix (Fin 3) (Fin 3) E) g a b := by
    intro x g a b j hj
    change (∑ j, (x j : G → Matrix (Fin 3) (Fin 3) E)) g a b = _
    rw [Finset.sum_apply, Matrix.sum_apply]
    refine Finset.sum_eq_single j (fun i _ hi => ?_) (by simp)
    exact (x i).2.2 g trivial a b fun hh => hi (hinj _ _ (hh.symm.trans hj))
  have hb : Function.Bijective f := by
    constructor
    · intro x y hxy
      funext j
      apply Subtype.ext
      funext g
      ext a b
      by_cases hj : wt a b = ((j : ℕ) : ℤ) - 2
      · rw [← hval x g a b j hj, ← hval y g a b j hj, hxy]
      · rw [(x j).2.2 g trivial a b hj, (y j).2.2 g trivial a b hj]
    · intro γ
      refine ⟨fun j => ⟨_, h (((j : ℕ) : ℤ) - 2) γ γ.2, fun g _ a b hab => ?_⟩, ?_⟩
      · simp only [Matrix.of_apply, if_neg hab]
      · apply Subtype.ext
        funext g
        ext a b
        obtain ⟨j, hj⟩ := wt_cases a b
        rw [hval _ g a b j hj]
        simp only [Matrix.of_apply, if_pos hj]
  rw [← (LinearEquiv.ofBijective f hb).finrank_eq, Module.finrank_pi_fintype]

theorem UpperTheory.finrank_local_cocycles_adjoint_unitaryThree_eq_twelve :
    LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O] [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E] [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E] [TopologicalSpace E] [IsModuleTopology ℚ_[l] E] [IsTopologicalRing E], finrank E ↥(finiteCocycles (MonoidHom.id _) (adRep (D.rz E))) = 12 := by
  intro hP l _ O _ _ _ _ _ _ _ D E _ _ _ _ _ _ _ _ _ _
  have H := fun j => UpperTheory.V.Loc.dim_Z1f_crystalline_deformation hP D E j
  haveI := (H 0).1
  rw [sum_dim _ fun j => (H j).2.2.1, Finset.sum_congr rfl fun j _ => (H _).2.1]
  decide
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LaWDUnr
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.WeilDeligne GlobalTheory.GalOfCusp GlobalTheory.HeckeGal GlobalTheory.LocLanglands GlobalTheory.Published UpperTheory.V.W
open GlobalTheory.Pst GlobalTheory.TripleGal Module
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000

private theorem abs_eig {L D : Type} [Field L] [AddCommGroup D] [Module L D] (U : (End L D)ˣ) (φ g : End L D)
    (hU : (U : End L D) = φ) (hc : φ * g = g * φ) (x : D) (hx0 : x ≠ 0) (s : L) (a b : ℕ) (k : ℤ)
    (hk : k = (b : ℤ) + -(a : ℤ)) (key : g ((φ ^ b) x) = s • (φ ^ a) x) :
    ∃ x' : D, x' ≠ 0 ∧ ∀ n : ℕ, (g * ((U ^ k : (End L D)ˣ) : End L D)) ((φ ^ n) x') = s • (φ ^ n) x' := by
  subst hU hk
  have k0 : g * ((U ^ ((b : ℤ) + -(a : ℤ)) : (End L D)ˣ) : End L D) * (U : End L D) ^ a = g * (U : End L D) ^ b := by
    rw [zpow_add, zpow_neg, zpow_natCast, zpow_natCast, ← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val,
      mul_assoc, ← Units.val_mul, inv_mul_cancel_right]
  refine ⟨((U : End L D) ^ a) x, fun h0 => hx0 ?_, fun n => ?_⟩
  · exact ((End.isUnit_iff _).1 (U.isUnit.pow a)).1 (h0.trans (map_zero _).symm)
  · have hc' : Commute (g * ((U ^ ((b : ℤ) + -(a : ℤ)) : (End L D)ˣ) : End L D)) ((U : End L D) ^ n) :=
      (Commute.mul_left hc.symm (Commute.units_zpow_right (Commute.refl _) _).symm).pow_right n
    rw [← End.mul_apply, hc'.eq, End.mul_apply, ← End.mul_apply _ _ x, k0, End.mul_apply, key, map_smul]

private theorem eig_of_frob {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ}
    [Fact l.Prime] (P : LocPrime l) {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw)
    (ι : Qbar l ≃+* ℂ) {L : FinExt l} {V : Type} [AddCommGroup V] [Module ↥L.1 V] [Module ℚ_[l] V]
    [IsScalarTower ℚ_[l] ↥L.1 V] [FiniteDimensional ↥L.1 V] (ρ : Representation ↥L.1 ↥(GK Bw.Kw) V)
    (h1 : finrank ↥L.1 V = 1) (hV : IsPst P ρ) (x : ↥(Dpst P ρ)) (hx0 : x ≠ 0) (σ : Weil h) (s : ↥L.1) {a b : ℕ}
    (hσ : ActsAs A (normV w) (σ : G F Ω) a b)
    (key : actD P ρ (weilToGK Bw h σ) ((phiD P ρ ^ (resDeg l w * b)) x) = s • (phiD P ρ ^ (resDeg l w * a)) x) :
    ι (s : Om l) ∈ (wdPst P ι Bw h hj ρ).eig σ := by
  have hfin := hV.finite
  have e1 : -alpha l σ = ((resDeg l w * b : ℕ) : ℤ) + -((resDeg l w * a : ℕ) : ℤ) := by
    rw [alpha, deg_eq hσ]; push_cast; ring
  obtain ⟨x', hx'0, k1⟩ := abs_eig (phiU P ρ) (phiD P ρ) (actD P ρ (weilToGK Bw h σ)) rfl (phiD_actD P ρ _) x hx0 s
    _ _ _ e1 key
  obtain ⟨n, hn⟩ : ∃ n : ℕ, wdMk P ι ρ ((phiD P ρ ^ n) x') ≠ 0 := by
    by_contra hc
    exact hx'0 (GlobalTheory.PstFaithful.eq_zero_of_wdMk_phiD_pow l P ι _ L _ _ _ fun n => not_not.1 fun hn => hc ⟨n, hn⟩)
  exact ParamAboveModel.mem_eig_wdPst P ι Bw h hj ρ _ h1 hV hn σ s (k1 n)

theorem UpperTheory.V.Loc.wdPotUnr :
    ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] {A : ValuationSubring Ω} {w : Plc F} (h : IsPlaceOver A w) {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l F Ω (Dec (F := F) A) O) (hj : GlobalTheory.Pst.Induces Bw) (ι : Qbar l ≃+* ℂ) (ψ : ↥(Dec (F := F) A) →* (Qbar l)ˣ), Continuous ψ → IsSmooth (ψ.comp (Subgroup.inclusion (Weil_le_Dec h))) → GlobalTheory.Pst.IsPstAt (UpperTheory.V.Loc.PP l) Bw (GlobalTheory.TripleGal.rk1 ψ) → ∀ σ : Weil h, ι (ψ (Subgroup.inclusion (Weil_le_Dec h) σ) : Qbar l) ∈ (GlobalTheory.Pst.wdAt (UpperTheory.V.Loc.PP l) ι Bw h hj (GlobalTheory.TripleGal.rk1 ψ)).eig σ := by
  intro F Ω _ _ _ _ _ l _ A w h O _ _ _ Bw hj ι ψ hψ hs hr σ
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  obtain ⟨L, r', hM, hV, e⟩ := wdAt_of_isPstAt ι Bw h hj hr
  rw [e]
  let m : ↥(GK Bw.Kw) →* (↥L.1)ˣ := (Matrix.GeneralLinearGroup.det.comp r').comp Bw.e.symm.toMonoidHom
  have hm0 : ∀ g, (m g : ↥L.1) = (r' (Bw.e.symm g) : Matrix (Fin 1) (Fin 1) ↥L.1) 0 0 := fun g => by
    simp [m, Matrix.det_unique]
  have hm : ∀ g, ((m g : ↥L.1) : Om l) = ψ (Bw.e.symm g) := fun g => by
    have := congrArg (fun f : ↥(Dec (F := F) A) →* GL (Fin 1) (Om l) =>
      (f (Bw.e.symm g) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0) hM.2
    rw [hm0]
    simpa [Formalism.MainNotions.N.mapRep, rk1] using this
  have hρ : ∀ g v, Bw.repE L r' g v = (m g : ↥L.1) • v := fun g v => by
    ext i
    fin_cases i
    simp [LocBridge.repE, hm0, Matrix.mulVec, dotProduct]
  obtain ⟨V, hV1, hV2⟩ := isOpen_induced_iff.1 hs
  have ho2 : IsOpen {g : GK Bw.Kw | ((Bw.e.symm g : Dec (F := F) A) : G F Ω) ∈ V} :=
    hV1.preimage (continuous_subtype_val.comp Bw.e_symm_cont)
  obtain ⟨U, hU, hU'⟩ := isOpen_induced_iff.1 ho2
  have h1 : (1 : GQ l) ∈ U := by
    have h0 : (1 : Ine (F := F) A) ∈ Subtype.val ⁻¹' V := by rw [hV2]; simp
    have : (1 : GK Bw.Kw) ∈ Subtype.val ⁻¹' U := by rw [hU']; simpa using h0
    exact this
  obtain ⟨K', hK1, hK2⟩ := (krullTopology_mem_nhds_one_iff _ _ U).1 (hU.mem_nhds h1)
  obtain ⟨x, hx0, hx⟩ := UpperTheory.exists_dpst_frobenius_eigenvector_of_character _ _ T Bw.Kw (supExt Bw.Kw ⟨K', hK1⟩) L le_sup_left m (Bw.repE L r') hρ
    (by simp only [hm]; exact Units.continuous_val.comp (hψ.comp Bw.e_symm_cont))
    (fun g hg hg' => by
      have h2 : g ∈ Subtype.val ⁻¹' U := hK2 (GK_le (K := ⟨K', hK1⟩) le_sup_right hg)
      rw [hU'] at h2
      have h3 : ((Bw.e.symm g : Dec (F := F) A) : G F Ω) ∈ Ine (F := F) A := by
        refine actsAs_zero_iff (q := 2).1 ⟨(Bw.e.symm g).2, fun y hy => ?_⟩
        rw [hj.valuation_lt_one_iff]
        simp only [pow_zero, pow_one]
        rw [map_sub, ← Bw.e_comm, MulEquiv.apply_symm_apply]
        exact GlobalTheory.FrobGen.norm_sub_lt hg' _ ((hj y).1 ((A.valuation_le_one_iff y).1 hy))
      have h4 : (⟨_, h3⟩ : Ine (F := F) A) ∈ Subtype.val ⁻¹' V := h2
      rw [hV2] at h4
      have h5 : ψ (Bw.e.symm g) = 1 := h4
      refine Units.ext (Subtype.ext ?_)
      rw [hm, h5]
      rfl)
  obtain ⟨a, b, hσ⟩ := σ.2
  have k2 := eig_of_frob (PP l) h Bw hj ι _ (by simp) hV x hx0 σ _ hσ
    (hx (weilToGK Bw h σ) _ _ (weilToGK_frobUr hj σ hσ))
  rw [hm] at k2
  simpa [weilToGK] using k2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.OrdDual
section
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Topology TrivSqZeroExt

namespace UpperTheory.V.Loc.OrdinaryDeformation

section Alg

variable {G R S : Type} [Group G] [CommRing R] [CommRing S] {m : ℕ}

private theorem adFun_map (f : R →+* S) (x : GG (m := m) (R := R)) (X : Matrix (Fin m) (Fin m) R) :
    (x.adFun X).map f = (GG.map f x).adFun (X.map f) := by
  have h1 : (thetaLie X).map f = thetaLie (X.map f) := by
    unfold thetaLie
    rw [Matrix.map_neg _ (map_neg f), Matrix.map_mul, Matrix.map_mul, Jmat_map, Matrix.transpose_map]
  have h2 : (((GG.map f x).left⁻¹ : GL (Fin m) S) : Matrix (Fin m) (Fin m) S) =
      ((x.left⁻¹ : GL (Fin m) R) : Matrix (Fin m) (Fin m) R).map f := rfl
  unfold GG.adFun
  rw [Matrix.map_mul, Matrix.map_mul, h2, GG.map_mat, GG.map_right]
  split_ifs
  · rfl
  · rw [h1]

private abbrev pr (R : Type) [CommRing R] : DualNumber R →+* R := (fstHom R R R : DualNumber R →+* R)

private abbrev inc (R : Type) [CommRing R] : R →+* DualNumber R := algebraMap R (DualNumber R)

private def ep (Y : Matrix (Fin m) (Fin m) R) : Matrix (Fin m) (Fin m) (DualNumber R) := Y.map inr

private theorem eps_smul (Z : Matrix (Fin m) (Fin m) (DualNumber R)) :
    (DualNumber.eps : DualNumber R) • Z = ep (Z.map (pr R)) := by
  ext a b <;> simp [ep]

private theorem inc_pr (Y : Matrix (Fin m) (Fin m) R) : (Y.map (inc R)).map (pr R) = Y := by
  ext a b; simp [algebraMap_eq_inl]

private theorem ep_eq (Y : Matrix (Fin m) (Fin m) R) : ep Y = (DualNumber.eps : DualNumber R) • Y.map (inc R) := by
  rw [eps_smul, inc_pr]

private theorem ep_mul (Y : Matrix (Fin m) (Fin m) R) (Z : Matrix (Fin m) (Fin m) (DualNumber R)) :
    ep Y * Z = ep (Y * Z.map (pr R)) := by
  rw [ep_eq, Matrix.smul_mul, eps_smul, Matrix.map_mul, inc_pr]

private theorem ad_ep (x : GG (m := m) (R := DualNumber R)) (Y : Matrix (Fin m) (Fin m) R) :
    GG.ad (m := m) (R := DualNumber R) x (ep Y) = ep ((GG.map (pr R) x).adFun Y) := by
  rw [ep_eq, map_smul, eps_smul, GG.ad_apply, adFun_map, inc_pr]

private theorem ep_add (X Y : Matrix (Fin m) (Fin m) R) : ep (X + Y) = ep X + ep Y := by
  ext a b <;> simp [ep]

private theorem ep_sub (X Y : Matrix (Fin m) (Fin m) R) : ep (X - Y) = ep X - ep Y := by
  ext a b <;> simp [ep]

private theorem ep_inj {X Y : Matrix (Fin m) (Fin m) R} (h : ep X = ep Y) : X = Y :=
  Matrix.ext fun a b => congrArg snd (congrFun (congrFun h a) b)

private theorem ep_pr (X : Matrix (Fin m) (Fin m) R) : (ep X).map (pr R) = 0 := by
  ext a b; simp [ep]

private theorem ker_sq : RingHom.ker (pr R) * RingHom.ker (pr R) = ⊥ := by
  refine le_bot_iff.1 (Ideal.mul_le.2 fun x hx y hy => ?_)
  have hx' : x.fst = 0 := hx
  have hy' : y.fst = 0 := hy
  rw [Ideal.mem_bot]
  ext <;> simp [hx', hy']

private theorem exists_coc (r : G →* GG (m := m) (R := R)) (r' : G →* GG (m := m) (R := DualNumber R))
    (h : (GG.map (pr R)).comp r' = r) :
    ∃ γ : G → Matrix (Fin m) (Fin m) R, IsCoc r γ ∧
      ∀ g, (r' g).mat = (r g).mat.map (inc R) + ep (γ g * (r g).mat) := by
  have e : (Ideal.Quotient.mk (RingHom.ker (pr R))).comp ((inc R).comp (pr R)) = Ideal.Quotient.mk _ := by
    refine RingHom.ext fun x => Ideal.Quotient.eq.2 ?_
    simp [RingHom.mem_ker, algebraMap_eq_inl]
  obtain ⟨γ', h1, h2, h3⟩ := exists_isCoc (RingHom.ker (pr R)) ((GG.map (inc R)).comp r) r' ker_sq (by
    rw [← h]
    refine MonoidHom.ext fun g => ?_
    simp only [MonoidHom.comp_apply, GG.map_map]
    rw [← RingHom.comp_assoc, RingHom.comp_assoc _ _ (Ideal.Quotient.mk _), e])
  have h4 : ∀ g, γ' g = ep ((γ' g).map snd) := fun g => by
    ext a b
    · exact h1 g a b
    · rfl
  have h5 : ∀ g, GG.map (pr R) (GG.map (inc R) (r g)) = r g := fun g =>
    SemidirectProduct.ext (Units.ext (inc_pr _)) rfl
  refine ⟨fun g => (γ' g).map snd, fun g k => ep_inj ?_, fun g => ?_⟩
  · rw [ep_add, ← h4, ← h4, h2 g k, h4 k]
    congr 1
    refine (ad_ep (R := R) (m := m) _ _).trans ?_
    rw [MonoidHom.comp_apply, h5]
    rfl
  · have e2 := ep_mul ((γ' g).map snd) (((GG.map (inc R)).comp r) g).mat
    rw [← h4, MonoidHom.comp_apply, GG.map_mat, inc_pr] at e2
    rw [(h3 g).2, Matrix.add_mul, Matrix.one_mul, MonoidHom.comp_apply, GG.map_mat, e2]

private theorem exists_conj (r : G →* GG (m := m) (R := R)) (r' : G →* GG (m := m) (R := DualNumber R))
    (h : (GG.map (pr R)).comp r' = r)
    (γ : G → Matrix (Fin m) (Fin m) R) (hγ : ∀ g, (r' g).mat = (r g).mat.map (inc R) + ep (γ g * (r g).mat))
    (X : Matrix (Fin m) (Fin m) R) :
    ∃ n : GL (Fin m) (DualNumber R), Matrix.GeneralLinearGroup.map (pr R) n = 1 ∧
      ((n⁻¹ : GL (Fin m) (DualNumber R)) : Matrix (Fin m) (Fin m) (DualNumber R)) - 1 = -ep X ∧
      ∀ g, (conjBy n r' g).mat = (r g).mat.map (inc R) + ep ((γ g + (X - adRep r g X)) * (r g).mat) := by
  obtain ⟨n, hn, hd⟩ := isDeform_cob (RingHom.ker (pr R)) r' (ep X) ker_sq (fun a b => rfl)
  have hg : ∀ g, GG.map (pr R) (r' g) = r g := fun g => DFunLike.congr_fun h g
  refine ⟨n, Units.ext ?_, ?_, fun g => ?_⟩
  · change (n : Matrix (Fin m) (Fin m) (DualNumber R)).map (pr R) = 1
    rw [hn, Matrix.map_add _ (map_add _), ep_pr, add_zero, Matrix.map_one _ (map_zero _) (map_one _)]
  · have h0 : ep X * ep X = 0 := by
      rw [ep_mul, ep_pr, Matrix.mul_zero]
      ext a b <;> simp [ep]
    have : ((n⁻¹ : GL (Fin m) (DualNumber R)) : Matrix (Fin m) (Fin m) (DualNumber R)) = 1 - ep X := by
      apply Units.inv_eq_of_mul_eq_one_right
      rw [hn, Matrix.add_mul, Matrix.mul_sub, Matrix.mul_sub, h0]
      simp
    rw [this]
    abel
  · have e : cob r' (ep X) g = ep (X - adRep r g X) := by
      rw [ep_sub, cob]
      congr 1
      refine (ad_ep (R := R) (m := m) _ _).trans ?_
      rw [hg]
      rfl
    rw [(hd g).2, e, Matrix.add_mul, Matrix.one_mul, ep_mul, ← GG.map_mat, hg, hγ g, Matrix.add_mul (γ g), ep_add,
      add_assoc]

end Alg

theorem rz_eq {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsLocalRing O] [Algebra ℤ_[l] O] (D : Dat3 l O)
    (E : Type) [CommRing E] [Algebra O E] :
    D.rz E = r0 D.η ((Units.map (algebraMap O E : O →* E)).comp D.Ψ) := by
  refine MonoidHom.ext fun g => SemidirectProduct.ext (Units.ext ?_) rfl
  show (tor O (D.Ψ g) : Matrix (Fin 3) (Fin 3) O).map (algebraMap O E) = tor _ (Units.map (algebraMap O E : O →* E) (D.Ψ g))
  rw [tor_val, tor_val, Matrix.diagonal_map (map_zero _)]
  congr 1
  funext i
  exact congrArg Units.val (map_zpow (Units.map (algebraMap O E : O →* E)) (D.Ψ g) (wt1 i))

theorem dual_ord (hP : LocalPublishedTheorems) {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O]
    [IsDiscreteValuationRing O] [CharZero O] [Algebra ℤ_[l] O] [Module.Finite ℤ_[l] O]
    [IsAdicComplete (maximalIdeal O) O] (D : Dat3 l O) (E : Type) [Field E] [Algebra ℚ_[l] E]
    [Module.Finite ℚ_[l] E] [Algebra O E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] O E] [IsScalarTower ℤ_[l] ℚ_[l] E]
    (r' : GQ l →* GG (m := 3) (R := DualNumber E)) (hr : D.InDcr (fstHom E E E : DualNumber E →+* E) r') :
    D.InDord (fstHom E E E : DualNumber E →+* E) r' := by
  haveI : Module.Finite ℚ_[l] (DualNumber E) := inferInstanceAs (Module.Finite ℚ_[l] (E × E))
  obtain ⟨γ, hc, hγ⟩ := exists_coc _ r' hr.red
  have c1 : ∀ a b, QCont l fun g => ((r' g).mat a b).fst := fun a b =>
    qcont_map (LinearMap.fst ℚ_[l] E E) (hr.cont a b)
  have c2 : ∀ a b, QCont l fun g => ((r' g).mat a b).snd := fun a b =>
    qcont_map (LinearMap.snd ℚ_[l] E E) (hr.cont a b)
  have hd : DualDef (D.rz E) γ r' := fun g => ⟨hr.mult g, fun a b => by
    rw [hγ g]
    ext <;> simp [ep, algebraMap_eq_inl]⟩
  obtain ⟨X, hX, hX'⟩ : ∃ X : Matrix (Fin 3) (Fin 3) E, (∀ a b, 0 ≤ wt a b → X a b = 0) ∧
      ∀ g a b, wt a b < 0 → (γ g + (X - adRep (D.rz E) g X)) a b = 0 := by
    letI : TopologicalSpace E := moduleTopology ℚ_[l] E
    haveI : IsModuleTopology ℚ_[l] E := ⟨rfl⟩
    haveI : IsTopologicalRing E := IsModuleTopology.isTopologicalRing ℚ_[l] E
    have d1 : Continuous fun g => (D.rz E g).mat := continuous_matrix fun a b => by
      have := c1 a b
      simp only [fun g => (hd g).2 a b] at this
      exact this
    have d2 : Continuous fun g => γ g * (D.rz E g).mat := continuous_matrix fun a b => by
      have := c2 a b
      simp only [fun g => (hd g).2 a b] at this
      exact this
    have d3 : Continuous γ := by
      have e : γ = fun g => γ g * (D.rz E g).mat * (D.rz E g⁻¹).mat := by
        funext g
        rw [Matrix.mul_assoc, rz_eq, GG.mat, GG.mat, unitaryThreeReflection_left, unitaryThreeReflection_left, ← Units.val_mul, ← map_mul, ← map_mul,
          mul_inv_cancel, map_one, map_one, Units.val_one, Matrix.mul_one]
      rw [e]
      exact d2.mul (d1.comp continuous_inv)
    have hf := ((dualCr D E (D.rz E) (fun _ => rfl) d1 γ ⟨d3, hc⟩ r' hd).1 hr.cr).2
    have key : ∀ j < (0 : ℤ), ∃ Y : Matrix (Fin 3) (Fin 3) E, ∀ g a b, wt a b = j →
        γ g a b = (adRep (D.rz E) g Y - Y) a b := fun j hj => by
      obtain ⟨-, -, h1, h2⟩ := dim_Z1f_crystalline_deformation hP D E j
      have h3 := h1 γ hf
      obtain ⟨Y, hY⟩ := (mem_coboundaries1 _ _).1 (((h2 _ h3.1 fun g a b h => if_neg h).1 hj).1 h3)
      refine ⟨Y, fun g a b h => ?_⟩
      rw [← hY g, Matrix.of_apply, if_pos h]
    choose Y hY using key
    refine ⟨Matrix.of fun a b => if h : wt a b < 0 then Y _ h a b else 0, fun a b h => dif_neg (not_lt.2 h),
      fun g a b h => ?_⟩
    have hw : wt b.rev a.rev = wt a b := by fin_cases a <;> fin_cases b <;> rfl
    have e : ∀ j (hj : j < 0), j = wt a b → Y j hj = Y _ h := by
      rintro j hj rfl; rfl
    rw [Matrix.add_apply, hY _ h g a b rfl, Matrix.sub_apply, Matrix.sub_apply, rz_eq, adRep_baseLift_apply, adRep_baseLift_apply,
      Matrix.of_apply, Matrix.of_apply, dite_eq_left h, dite_eq_left (hw ▸ h), e _ _ hw]
    ring
  obtain ⟨n, hn1, hn2, hn3⟩ := exists_conj _ r' hr.red γ hγ X
  refine ⟨conjBy n r', n⁻¹, ⟨dcr_conj hr n hn1, fun g a b h => ?_⟩, (congOne_iff _ _).2 (by rw [map_inv, hn1, inv_one]),
    fun a b h => ?_, (conjBy_inv_conjBy n r').symm⟩
  · have hab : a ≠ b := by
      rintro rfl
      simp [wt] at h
    have h0 := hX' g a b h
    rw [hn3 g]
    generalize γ g + (X - adRep (D.rz E) g X) = Z at h0
    rw [rz_eq, GG.mat, unitaryThreeReflection_left, tor_val]
    simp [ep, Matrix.mul_diagonal, h0, Matrix.diagonal_apply_ne _ hab]
  · rw [hn2]
    simp [ep, hX a b h]

end UpperTheory.V.Loc.OrdinaryDeformation
end

