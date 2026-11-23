module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.Bundle0006
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedIsCrysAndJumpEqZero
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TateDefs
public import ReciprocityTheory.GroupCohomology.ImportsAlt

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrysOfInertia
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private theorem exists_int_basis {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [CompactSpace G]
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V]
    [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] G V) (hρ : ∀ x, Continuous fun g => ρ g x) :
    ∃ (n : ℕ) (e : Basis (Fin n) ℚ_[l] V), ∀ g i j, ‖e.repr (ρ g (e j)) i‖ ≤ 1 := by
  classical
  letI : Module ℤ_[l] V := Module.compHom V (algebraMap ℤ_[l] ℚ_[l])
  haveI : IsScalarTower ℤ_[l] ℚ_[l] V := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  let e₀ := Module.finBasis ℚ_[l] V
  let Λ : Submodule ℤ_[l] V := Submodule.span ℤ_[l] (Set.range fun p : G × Fin (finrank ℚ_[l] V) => ρ p.1 (e₀ p.2))
  have hc : Continuous fun g : G => (fun i j => e₀.repr (ρ g (e₀ j)) i) :=
    continuous_pi fun i => continuous_pi fun j =>
      (IsModuleTopology.continuous_of_linearMap (e₀.coord i)).comp (hρ _)
  obtain ⟨C, hC⟩ := (isCompact_range hc).isBounded.exists_norm_le
  obtain ⟨c, hc0, hcC⟩ : ∃ c : ℚ_[l], c ≠ 0 ∧ C ≤ ‖c‖ := by
    obtain ⟨c, hc⟩ := NormedField.exists_lt_norm ℚ_[l] (max C 0)
    exact ⟨c, norm_pos_iff.1 (lt_of_le_of_lt (le_max_right _ _) hc), ((le_max_left _ _).trans hc.le)⟩
  have hle : Λ ≤ Submodule.span ℤ_[l] (Set.range fun i => c • e₀ i) := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨⟨g, j⟩, rfl⟩
    change ρ g (e₀ j) ∈ _
    rw [← e₀.sum_repr (ρ g (e₀ j))]
    refine Submodule.sum_mem _ fun i _ => ?_
    have h1 : ‖e₀.repr (ρ g (e₀ j)) i / c‖ ≤ 1 := by
      rw [norm_div]
      refine div_le_one_of_le₀ (le_trans ?_ hcC) (norm_nonneg _)
      exact ((norm_le_pi_norm _ j).trans (norm_le_pi_norm (fun i j => e₀.repr (ρ g (e₀ j)) i) i)).trans
        (hC _ ⟨g, rfl⟩)
    let z : ℤ_[l] := ⟨_, h1⟩
    have h2 : e₀.repr (ρ g (e₀ j)) i • e₀ i = z • c • e₀ i := by
      change _ = (e₀.repr (ρ g (e₀ j)) i / c) • c • e₀ i
      rw [smul_smul, div_mul_cancel₀ _ hc0]
    rw [h2]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  haveI : Submodule.IsLattice ℚ_[l] Λ :=
    Submodule.IsLattice.of_fg ℚ_[l] ((Submodule.fg_span (Set.finite_range _)).of_le hle)
  haveI : Submodule.IsFullLattice ℚ_[l] Λ :=
    { span_eq_top := by
        rw [eq_top_iff, ← e₀.span_eq]
        refine Submodule.span_mono ?_
        rintro _ ⟨i, rfl⟩
        exact Submodule.subset_span ⟨(1, i), by simp⟩ }
  haveI : Module.Free ℤ_[l] Λ := Submodule.IsLattice.free ℚ_[l] Λ
  haveI : Module.Finite ℤ_[l] Λ := Submodule.IsLattice.finite ℚ_[l] Λ
  let b := Module.finBasis ℤ_[l] Λ
  have hst : ∀ g, ∀ x ∈ Λ, ρ g x ∈ Λ := by
    intro g x hx
    induction hx using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨⟨h, j⟩, rfl⟩ := hx
      exact Submodule.subset_span ⟨(g * h, j), by simp⟩
    | zero => simp
    | add x y _ _ hx hy => rw [map_add (f := _)]; exact Λ.add_mem hx hy
    | smul a x _ hx => rw [LinearMap.map_smul_of_tower]; exact Λ.smul_mem a hx
  refine ⟨_, b.extendOfIsFullLattice ℚ_[l], fun g i j => ?_⟩
  have h1 : ρ g (b.extendOfIsFullLattice ℚ_[l] j) =
      ∑ k, ((b.repr ⟨_, hst g _ (b j).2⟩ k : ℤ_[l]) : ℚ_[l]) • b.extendOfIsFullLattice ℚ_[l] k := by
    have := congrArg Λ.subtype (b.sum_repr ⟨_, hst g _ (b j).2⟩)
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_sum] at this
    convert this.symm using 1
    · rw [Basis.extendOfIsFullLattice_apply]; rfl
    · apply Finset.sum_congr rfl
      intro k hk
      rw [Basis.extendOfIsFullLattice_apply]
      rfl
  rw [h1, Basis.repr_sum_self]
  exact PadicInt.norm_le_one _


open GlobalTheory.UnramifiedRep GlobalTheory.UnramifiedCrys GlobalTheory.Cyc in
private theorem isCrys_of_inertia {l : ℕ} [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (Ti : LocTied l P AI)
    (K : FinExt l) (hχ : Continuous fun g => (((P.PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]))
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V]
    [IsModuleTopology ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) (hρ : ∀ x, Continuous fun g => ρ g x) (w : ℤ)
    (hI : ∀ g ∈ IK K, ∀ x, ρ g x = (((P.PD K).χ g ^ w : ℚ_[l]ˣ) : ℚ_[l]) • x) : IsCrys (P.PD K) ρ := by
  have := compactSpace_GK K
  let χ := (P.PD K).χ
  let ρ' : Representation ℚ_[l] ↥(GK K) V := twist (χ ^ (-w)) ρ
  have hρ' : ∀ g x, ρ' g x = ((χ g ^ (-w) : ℚ_[l]ˣ) : ℚ_[l]) • ρ g x := fun g x => rfl
  have hcont : ∀ x, Continuous fun g => ρ' g x := fun x => by
    simp only [hρ', Units.val_zpow_eq_zpow_val]
    exact (hχ.zpow₀ _ fun g => Or.inl (Units.ne_zero _)).smul (hρ x)
  have hI' : ∀ g ∈ IK K, ∀ x, ρ' g x = x := fun g hg x => by
    rw [hρ', hI g hg, smul_smul, ← Units.val_mul, ← zpow_add, neg_add_cancel, zpow_zero, Units.val_one, one_smul]
  obtain ⟨n, e, hint⟩ := exists_int_basis ρ' hcont
  obtain ⟨M, hM⟩ := exists_matrixHom ρ' e hint
  obtain ⟨W, hW, hWg⟩ := exists_witt_matrix (p := l) (AI.actT.comp (GK K).subtype)
    (fun y m hm hy => (continuous_subtype_val.tendsto (1 : ↥(GK K))).eventually
      (eventually_actT_eq AI y m hm hy)) M
    (continuous_pi fun i => continuous_pi fun j => continuous_induced_rng.2 (by
      have h := (IsModuleTopology.continuous_of_linearMap (e.coord i)).comp (hcont (e j))
      exact h.congr fun g => (hM g i j).symm))
    (fun g hg => by
      have h := hI' g (Subgroup.subset_closure fun x hx =>
        norm_sub_lt_one_of_fix AI g (fun m hm y hy => hg m hm y hy) x hx)
      rw [← map_one M]
      ext i j
      rw [hM, hM, h, map_one, Module.End.one_apply])
  have hB : ∀ g, (Matrix.of fun i j => algebraMap ℚ_[l] P.R.B (e.repr (ρ' g (e j)) i)) *
      (AI.ιA.mapMatrix W).map ((P.PD K).actB g) = AI.ιA.mapMatrix W := fun g => by
    conv_rhs => rw [← hWg g, map_mul]
    congr 1
    · ext i j
      rw [Matrix.of_apply, ← hM]
      exact (ιA_zlW AI Ti (M g i j)).symm
    · ext i j
      exact (P.PD_actB K g _).trans (AI.ιA_act g _).symm
  obtain ⟨u, hu⟩ := (P.PD K).t_unit
  have hact : ∀ g, (P.PD K).actB g ((u ^ (-w) : (P.R.B)ˣ) : P.R.B) =
      algebraMap ℚ_[l] P.R.B ((χ g ^ (-w) : ℚ_[l]ˣ) : ℚ_[l]) * ((u ^ (-w) : (P.R.B)ˣ) : P.R.B) := fun g => by
    have h1 : Units.map ((P.PD K).actB g : P.R.B →* P.R.B) u =
        Units.map (algebraMap ℚ_[l] P.R.B : ℚ_[l] →* P.R.B) (χ g) * u := by
      ext
      change (P.PD K).actB g u = algebraMap ℚ_[l] P.R.B (χ g : ℚ_[l]ˣ) * u
      rw [hu, (P.PD K).t_act, Algebra.smul_def]
    have h2 := congrArg (fun x : (P.R.B)ˣ => ((x ^ (-w) : (P.R.B)ˣ) : P.R.B)) h1
    beta_reduce at h2
    rw [mul_zpow, ← map_zpow, ← map_zpow, Units.val_mul] at h2
    exact h2
  refine GlobalTheory.T.isCrys_of_split_alt (P.PD K) ρ e (((u ^ (-w) : (P.R.B)ˣ) : P.R.B) • AI.ιA.mapMatrix W) ?_ fun g => ?_
  · rw [Matrix.det_smul, ← RingHom.map_det]
    exact ((Units.isUnit _).pow _).mul (hW.map _)
  · conv_rhs => rw [← hB g]
    ext i j
    simp only [Matrix.mul_apply, Matrix.smul_apply, Matrix.map_apply, Matrix.of_apply, smul_eq_mul, map_mul, hact,
      hρ', map_smul, Finsupp.smul_apply, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => by ring

theorem UpperTheory.V.Loc.crUnr :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {A : Type} [CommRing A] [Algebra ℚ_[l] A] [Algebra ℤ_[l] A] [IsScalarTower ℤ_[l] ℚ_[l] A] {V : Type} [AddCommGroup V] [Module A V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [FiniteDimensional ℚ_[l] V] [TopologicalSpace V] [IsModuleTopology ℚ_[l] V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] (ρ : Representation A G V), ContAction ρ → ∀ w : ℤ, (∀ g, φ g ∈ Iq l → ∀ x, ρ g x = ((cycA l l A (φ g) ^ w : Aˣ) : A) • x) → IsCr φ ρ := by
  intro l _ G _ _ _ φ hφ A _ _ _ _ V _ _ _ _ _ _ _ _ _ ρ hρ w hI
  obtain ⟨K, e, -, he, hφe, hr, -⟩ := openField φ hφ
  obtain ⟨T⟩ := tiedP l
  obtain ⟨hc, -, hq⟩ := cycFacts l l
  have hφ' : ∀ g : ↥(GK K), φ (e.symm g) = g := fun g => by
    rw [← hφe]
    simp
  let ρ' : Representation A ↥(GK K) V := ρ.comp e.symm.toMonoidHom
  have hχ : ∀ g : ↥(GK K), ((((PP l).PD K).χ g : ℚ_[l]ˣ) : ℚ_[l]) = (((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) : ℚ_[l]) :=
    fun g => by rw [(PP l).PD_χ, hq]
  have h1 : Crys K ρ' := by
    refine isCrys_of_inertia (PP l) (AIP l) T K ?_ _ (fun x => ?_) w fun g hg x => ?_
    · simp only [hχ]
      have h0 : Continuous fun g : ↥(GK K) => ((cyc l l g : ℤ_[l]ˣ) : ℤ_[l]) :=
        Units.continuous_val.comp (hc.comp continuous_subtype_val)
      exact continuous_subtype_val.comp h0
    · exact hρ.comp (he.prodMk continuous_const)
    · change ρ (e.symm g) x = _
      rw [hI _ (by rw [hφ']; exact (memIK K g).1 hg), hφ']
      have h2 : cycA l l A g = Units.map (algebraMap ℚ_[l] A : ℚ_[l] →* A) (((PP l).PD K).χ g) := by
        ext
        change algebraMap ℤ_[l] A _ = algebraMap ℚ_[l] A _
        rw [hχ, IsScalarTower.algebraMap_apply ℤ_[l] ℚ_[l] A]
        rfl
      rw [h2, ← map_zpow]
      exact algebraMap_smul A _ x
  have h2 := (isCrIff K ρ').1.2 h1
  have h3 : Dcr φ (resCoef ℚ_[l] ρ) = Dcr (GK K).subtype (resCoef ℚ_[l] ρ') := by
    unfold Dcr
    refine (e.symm.surjective.iInf_congr _ fun g => ?_).symm
    unfold actC
    rw [hφ']
    rfl
  unfold IsCr at h2 ⊢
  rw [h3, h2, hr, Subgroup.range_subtype]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LatticeCochainsFinGenOfFinLevel
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

section
open ReciprocityTheory.Coh
variable {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {n : ℕ}

private noncomputable def redT (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) (m : ℕ) :
    TRep ℤ_[l] G :=
  { V := (Fin n → ℤ_[l]) ⧸ lSub l (Fin n → ℤ_[l]) (m + 1)
    ccs := ⟨fun _ => continuous_of_discreteTopology⟩
    rho := redRep ρ (m + 1)
    cont := contAction_redRep h (m + 1) }

private instance redT_disc (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) (m : ℕ) :
    DiscreteTopology (redT ρ h m).V := discrete_quot_lSub l n (m + 1)

private instance redT_fin (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) (m : ℕ) :
    Finite (redT ρ h m).V := finite_quot_lSub l n (m + 1)

private theorem lSub_le {X : Type} [AddCommGroup X] [Module ℤ_[l] X] (m : ℕ) :
    lSub l X (m + 1) ≤ (lSub l X m).comap LinearMap.id := by
  intro x hx
  obtain ⟨y, rfl⟩ := mem_lSub.mp hx
  show (l : ℤ_[l]) ^ (m + 1) • y ∈ lSub l X m
  exact mem_lSub.mpr ⟨(l : ℤ_[l]) • y, by rw [pow_succ, mul_smul]⟩

private noncomputable def tauL (l : ℕ) [Fact l.Prime] (X : Type) [AddCommGroup X] [Module ℤ_[l] X] (m : ℕ) :
    (X ⧸ lSub l X (m + 1)) →ₗ[ℤ_[l]] (X ⧸ lSub l X m) :=
  Submodule.mapQ _ _ LinearMap.id (lSub_le m)

private theorem tauL_mk {X : Type} [AddCommGroup X] [Module ℤ_[l] X] (m : ℕ) (x : X) :
    tauL l X m (Submodule.Quotient.mk x) = Submodule.Quotient.mk x := rfl

omit [TopologicalSpace G] [IsTopologicalGroup G] in
private theorem tauL_equiv {X : Type} [AddCommGroup X] [Module ℤ_[l] X] (ρ : Representation ℤ_[l] G X) (m : ℕ)
    (g : G) (y : X ⧸ lSub l X (m + 1)) : tauL l X m (redRep ρ (m + 1) g y) = redRep ρ m g (tauL l X m y) := by
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  rw [redRep_mk, tauL_mk, tauL_mk, redRep_mk]

private theorem tauL_surj {X : Type} [AddCommGroup X] [Module ℤ_[l] X] (m : ℕ) :
    Function.Surjective (tauL l X m) := by
  intro y
  obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective _ y
  exact ⟨Submodule.Quotient.mk x, rfl⟩

private noncomputable def tauT (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) (m : ℕ) :
    Pair (redT ρ h (m + 1)) (redT ρ h m) :=
  Pair.ofMap (M := redT ρ h (m + 1)) (M' := redT ρ h m)
    (tauL l (Fin n → ℤ_[l]) (m + 1)) continuous_of_discreteTopology (tauL_equiv ρ (m + 1))

private noncomputable def piT (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) (m : ℕ) :
    Pair ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G) (redT ρ h m) :=
  Pair.ofMap (M := ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G)) (M' := redT ρ h m)
    (lSub l (Fin n → ℤ_[l]) (m + 1)).mkQ (continuous_mkQ _) (fun g x => (redRep_mk ρ (m + 1) g x).symm)

private theorem eq_zero_of_lSub (x : Fin n → ℤ_[l]) (hx : ∀ m, x ∈ lSub l (Fin n → ℤ_[l]) (m + 1)) : x = 0 := by
  funext i
  apply PadicInt.ext_of_toZModPow.mp
  intro k
  rw [Pi.zero_apply, map_zero]
  cases k with
  | zero =>
    haveI : Subsingleton (ZMod (l ^ 0)) := ZMod.subsingleton_iff.mpr (pow_zero _)
    exact Subsingleton.elim _ _
  | succ k => exact mem_lSub_pi.mp (hx k) i

private theorem towerLim (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ) :
    Cx.IsTowerLim (fun m => (redT ρ h m).coch) (fun m => (tauT ρ h m).hom)
      (TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : TRep ℤ_[l] G)) fun m => (piT ρ h m).hom := by
  refine limRep_holds ℤ_[l] G (fun m => redT ρ h m) (tauT ρ h) _ (piT ρ h)
    (fun m => ⟨rfl, rfl, tauL_surj (m + 1), fun x => rfl⟩) ?_ ?_
  · have hc : Continuous fun (x : Fin n → ℤ_[l]) (m : ℕ) => (piT ρ h m).u x :=
      continuous_pi fun m => (piT ρ h m).u_cont
    refine (hc.isClosedEmbedding ?_).isEmbedding
    intro x y hxy
    rw [← sub_eq_zero]
    apply eq_zero_of_lSub
    intro m
    have := congr_fun hxy m
    exact (Submodule.Quotient.eq _).mp this
  · intro y hy
    let S : ℕ → Set (Fin n → ℤ_[l]) := fun m => (piT ρ h m).u ⁻¹' {y m}
    have hS : (⋂ m, S m).Nonempty := by
      apply IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S
      · intro m x hx
        show (piT ρ h m).u x = y m
        have hx' : (piT ρ h (m + 1)).u x = y (m + 1) := hx
        rw [← hy m, ← hx']
        rfl
      · intro m
        obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (y m)
        exact ⟨x, hx⟩
      · exact isCompact_univ.of_isClosed_subset
          ((isClosed_singleton).preimage (piT ρ h 0).u_cont) (Set.subset_univ _)
      · intro m
        exact (isClosed_singleton).preimage (piT ρ h m).u_cont
    obtain ⟨x, hx⟩ := hS
    exact ⟨x, fun m => Set.mem_iInter.mp hx m⟩

private theorem smul_emb (m : ℕ) : IsEmbedding fun x : Fin n → ℤ_[l] => (l : ℤ_[l]) ^ m • x := by
  have hc : (l : ℤ_[l]) ^ m ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero)
  refine (Continuous.isClosedEmbedding (continuous_const_smul _) ?_).isEmbedding
  intro x y hxy
  funext i
  have := congr_fun hxy i
  simp only [Pi.smul_apply, smul_eq_mul] at this
  exact mul_left_cancel₀ hc this

private theorem finH {χ : G →* ℤ_[l]ˣ} {d : ℕ} (hF : FinLevel l G χ d) (M : TRep ℤ_[l] G) [Finite M.V]
    [DiscreteTopology M.V] : (∀ k, Finite (M.H k)) ∧ ∀ k, 2 < k → Subsingleton (M.H k) := by
  obtain ⟨h1, h2, h3, -, -⟩ := hF M.V M.rho M.cont
  obtain ⟨hN, ⟨e0, -⟩, ⟨e1, -⟩, ⟨e2, -⟩⟩ := low_holds ℤ_[l] G M
  refine ⟨fun k => ?_, fun k hk => ?_⟩
  · match k with
    | 0 => exact Finite.of_equiv _ e0.symm.toEquiv
    | 1 => exact Finite.of_equiv _ e1.symm.toEquiv
    | 2 => exact Finite.of_equiv _ e2.symm.toEquiv
    | k + 3 =>
      obtain ⟨e, -⟩ := hN (k + 3)
      haveI := h3 (k + 3) (by omega)
      exact Finite.of_equiv _ e.symm.toEquiv
  · obtain ⟨e, -⟩ := hN k
    haveI := h3 k (by omega)
    exact e.toEquiv.subsingleton

end

theorem UpperTheory.latticeCochains_finGen_of_finLevel :
    ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] {χ : G →* ℤ_[l]ˣ} {d : ℕ}, FinLevel l G χ d → ∀ {n : ℕ} (ρ : Representation ℤ_[l] G (Fin n → ℤ_[l])) (h : ContAction ρ), ReciprocityTheory.Coh.Cx.FinGen (ReciprocityTheory.Coh.TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : ReciprocityTheory.Coh.TRep ℤ_[l] G)) 2 := by
  intro l _ G _ _ _ χ d hF n ρ h
  haveI : IsAdicComplete (Ideal.span {(l : ℤ_[l])}) ℤ_[l] :=
    PadicInt.maximalIdeal_eq_span_p (p := l) ▸ inferInstance
  have hl : (l : ℤ_[l]) ≠ 0 := Nat.cast_ne_zero.mpr (Fact.out : l.Prime).ne_zero
  have hT := towerLim ρ h
  have htors : ∀ (k : ℕ) (x : (ReciprocityTheory.Coh.TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : ReciprocityTheory.Coh.TRep ℤ_[l] G)).X k),
      (l : ℤ_[l]) • x = 0 → x = 0 := by
    intro k x hx
    apply Subtype.ext
    funext g
    have := congr_arg (fun z : (ReciprocityTheory.Coh.TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : ReciprocityTheory.Coh.TRep ℤ_[l] G)).X k =>
      z.1 g) hx
    exact (smul_eq_zero.mp this).resolve_left hl
  have hker : ∀ (m k : ℕ) (x : (ReciprocityTheory.Coh.TRep.coch ({ V := Fin n → ℤ_[l], rho := ρ, cont := h } : ReciprocityTheory.Coh.TRep ℤ_[l] G)).X k),
      ((piT ρ h m).hom.f k) x = 0 ↔ ∃ y, x = (l : ℤ_[l]) ^ (m + 1) • y := by
    intro m k x
    have key : ((piT ρ h m).hom.f k) x = 0 ↔
        ∀ g, x.1 g ∈ lSub l (Fin n → ℤ_[l]) (m + 1) := by
      constructor
      · intro hx g
        have := congr_arg (fun z : (ReciprocityTheory.Coh.TRep.coch (redT ρ h m)).X k =>
          z.1 g) hx
        exact (Submodule.Quotient.mk_eq_zero _).mp this
      · intro hx
        apply Subtype.ext
        funext g
        exact (Submodule.Quotient.mk_eq_zero _).mpr (hx g)
    rw [key]
    constructor
    · intro hx
      choose y hy using fun g => mem_lSub.mp (hx g)
      have hyc : Continuous y := by
        apply (smul_emb (n := n) (l := l) (m + 1)).continuous_iff.mpr
        have : (fun x : Fin n → ℤ_[l] => (l : ℤ_[l]) ^ (m + 1) • x) ∘ y =
            x.1 := funext hy
        rw [this]
        exact x.2
      refine ⟨⟨y, hyc⟩, ?_⟩
      apply Subtype.ext
      funext g
      exact (hy g).symm
    · rintro ⟨y, rfl⟩ g
      exact mem_lSub.mpr ⟨y.1 g, rfl⟩
  have hfin : ∀ m, (∀ k, Finite ((redT ρ h m).H k)) ∧ ∀ k, 2 < k → Subsingleton ((redT ρ h m).H k) :=
    fun m => finH hF (redT ρ h m)
  have hlen0 : ∀ k, IsFiniteLength ℤ_[l] ((redT ρ h 0).coch.H k) := fun k => by
    haveI := (hfin 0).1 k
    exact isFiniteLength_iff_isNoetherian_isArtinian.mpr ⟨inferInstance, inferInstance⟩
  have res := ReciprocityTheory.Coh.finGen_holds ℤ_[l] (l : ℤ_[l]) _ _ _ _ hT htors hker hlen0
  refine ⟨fun k => (res k).1, fun k hk => ?_⟩
  have ext := (ReciprocityTheory.Coh.tower_holds ℤ_[l] _ _ _ _ hT k).2 (fun j _ m => by
    haveI := (hfin m).1 j
    infer_instance)
  refine ⟨fun a b => ?_⟩
  have ha := ext a (fun m => by
    haveI := (hfin m).2 k hk
    exact Subsingleton.elim _ _)
  have hb := ext b (fun m => by
    haveI := (hfin m).2 k hk
    exact Subsingleton.elim _ _)
  rw [ha, hb]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.NonemptyCohomologyRestrictScalarsLinearEquiv
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc Topology

private def subEq {Q A X : Type} [CommRing Q] [CommRing A] [Algebra Q A] [AddCommGroup X] [Module A X]
    [Module Q X] [IsScalarTower Q A X] (Z' : Submodule Q X) (Z : Submodule A X)
    (hZ : ∀ x, x ∈ Z' ↔ x ∈ Z) : Z' ≃ₗ[Q] Z where
  toFun x := ⟨x.1, (hZ _).1 x.2⟩
  invFun x := ⟨x.1, (hZ _).2 x.2⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := rfl
  right_inv _ := rfl

private theorem quotEq {Q A X : Type} [CommRing Q] [CommRing A] [Algebra Q A] [AddCommGroup X] [Module A X]
    [Module Q X] [IsScalarTower Q A X] (Z' B' : Submodule Q X) (Z B : Submodule A X)
    (hZ : ∀ x, x ∈ Z' ↔ x ∈ Z) (hB : ∀ x, x ∈ B' ↔ x ∈ B) :
    Nonempty ((Z' ⧸ B'.comap Z'.subtype) ≃ₗ[Q] (Z ⧸ B.comap Z.subtype)) := by
  refine ⟨(Submodule.Quotient.equiv (B'.comap Z'.subtype) ((B.comap Z.subtype).restrictScalars Q)
    (subEq Z' Z hZ) ?_).trans (Submodule.Quotient.restrictScalarsEquiv Q (B.comap Z.subtype))⟩
  ext ⟨x, hx⟩
  rw [Submodule.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have : (y : X) = x := congrArg Subtype.val hyx
    show x ∈ B
    rw [← this]
    exact (hB _).1 hy
  · intro h
    exact ⟨⟨x, (hZ x).2 hx⟩, (hB x).2 h, rfl⟩

theorem UpperTheory.nonempty_cohomology_restrictScalars_linearEquiv :
    ∀ (Q : Type) {A : Type} [CommRing Q] [CommRing A] [Algebra Q A] {G : Type} [Group G] [TopologicalSpace G] {V : Type} [AddCommGroup V] [Module A V] [Module Q V] [IsScalarTower Q A V] [TopologicalSpace V] [IsTopologicalAddGroup V] [ContinuousConstSMul A V] [ContinuousConstSMul Q V] (ρ : Representation A G V), Nonempty (↥(H0 (resCoef Q ρ)) ≃ₗ[Q] ↥(H0 ρ)) ∧ Nonempty (H1 (resCoef Q ρ) ≃ₗ[Q] H1 ρ) ∧ Nonempty (H2 (resCoef Q ρ) ≃ₗ[Q] H2 ρ) ∧ ∀ n, Nonempty (Hn (resCoef Q ρ) n ≃ₗ[Q] Hn ρ n) := by
  intro Q A _ _ _ G _ _ V _ _ _ _ _ _ _ _ ρ
  have hd : ∀ n (f : (Fin n → G) → V), dn (resCoef Q ρ) n f = dn ρ n f := by
    intro n f
    funext g
    rw [dn_apply, dn_apply]
    congr 1
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← algebraMap_smul A ((-1 : Q) ^ ((j : ℕ) + 1))]
    simp
  refine ⟨⟨subEq _ _ fun x => Iff.rfl⟩, quotEq _ _ _ _ (fun x => Iff.rfl) ?_,
    quotEq _ _ _ _ (fun x => Iff.rfl) ?_, fun n => quotEq _ _ _ _ ?_ ?_⟩
  · intro x
    simp only [ReciprocityTheory.Gal.B1, LinearMap.mem_range]
    exact Iff.rfl
  · intro x
    simp only [ReciprocityTheory.Gal.B2, Submodule.mem_map, mem_contMaps]
    exact Iff.rfl
  · intro x
    simp only [ReciprocityTheory.Gal.Zn, Submodule.mem_inf, LinearMap.mem_ker, ReciprocityTheory.Gal.Cn,
      mem_contMaps, hd]
  · intro x
    cases n with
    | zero => simp [ReciprocityTheory.Gal.Bn]
    | succ n => simp only [ReciprocityTheory.Gal.Bn, Submodule.mem_map, ReciprocityTheory.Gal.Cn, mem_contMaps, hd]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TypeConj
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal TensorProduct Module UpperTheory.V.Loc UpperTheory.V.U3

section Gen

variable {Q A V V' : Type} [Field Q] [CommRing A] [Algebra Q A] [AddCommGroup V] [Module A V] [Module Q V]
  [IsScalarTower Q A V] [AddCommGroup V'] [Module A V'] [Module Q V'] [IsScalarTower Q A V']

private noncomputable def tr (B : Type) [AddCommGroup B] [Module Q B] (e : V ≃ₗ[A] V') :
    V ⊗[Q] B ≃ₗ[A] V' ⊗[Q] B := AlgebraTensorModule.congr e (LinearEquiv.refl Q B)

variable {B B' : Type} [AddCommGroup B] [Module Q B] [AddCommGroup B'] [Module Q B'] (e : V ≃ₗ[A] V')

private theorem tr_map {f : V →ₗ[A] V} {f' : V' →ₗ[A] V'} (h : ∀ x, e (f x) = f' (e x)) (b : B →ₗ[Q] B')
    (x : V ⊗[Q] B) :
    tr B' e (AlgebraTensorModule.map f b x) = AlgebraTensorModule.map f' b (tr B e x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v c => simp [tr, h]
  | add x y hx hy => simp only [map_add (f := _), hx, hy]

private theorem tr_smul {K : Type} [AddCommGroup K] [Module Q K] (s : K →ₗ[Q] Module.End Q B) (c : A ⊗[Q] K)
    (x : V ⊗[Q] B) :
    tr B e (((TensorProduct.homTensorHomMap (RingHom.id Q) V B V B).comp
      (TensorProduct.map (Algebra.lsmul Q Q V : A →ₐ[Q] Module.End Q V).toLinearMap s)) c x) =
    ((TensorProduct.homTensorHomMap (RingHom.id Q) V' B V' B).comp
      (TensorProduct.map (Algebra.lsmul Q Q V' : A →ₐ[Q] Module.End Q V').toLinearMap s)) c (tr B e x) := by
  induction c using TensorProduct.induction_on with
  | zero => simp
  | add c d hc hd => simp only [map_add (f := _), LinearMap.add_apply, hc, hd]
  | tmul a k =>
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v c => simp [tr]
    | add x y hx hy => simp only [map_add (f := _), hx, hy]

end Gen

section Per

variable {l : ℕ} [Fact l.Prime] {A V V' : Type} [CommRing A] [Algebra ℚ_[l] A] [AddCommGroup V] [Module A V]
  [Module ℚ_[l] V] [IsScalarTower ℚ_[l] A V] [AddCommGroup V'] [Module A V'] [Module ℚ_[l] V']
  [IsScalarTower ℚ_[l] A V'] (e : V ≃ₗ[A] V')

end Per
end

