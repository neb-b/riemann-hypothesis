module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.BaseRepGL3NormalisedOfPsiEqOne

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.AdRepBaseLiftApply
section
open Matrix UpperTheory.V.U3

private theorem UpperTheory.V.U3.theta_lie_apply {R : Type} [CommRing R] (X : Matrix (Fin 3) (Fin 3) R)
    (a b : Fin 3) : thetaLie X a b = -X b.rev a.rev := by
  simp only [thetaLie, Matrix.neg_apply, Matrix.mul_apply, Jmat, Matrix.transpose_apply]
  congr 1
  simp only [ite_mul, mul_ite, one_mul, zero_mul, mul_zero, Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
  rw [Finset.sum_eq_single b.rev]
  · simp
  · intro x _ hx
    rw [if_neg]
    intro h
    exact hx (by rw [h, Fin.rev_rev])
  · simp

theorem UpperTheory.V.U3.adRep_baseLift_apply :
    ∀ {G R : Type} [Group G] [CommRing R] (η : G →* ℤˣ) (Ψ : G →* Rˣ) (g : G) (X : Matrix (Fin 3) (Fin 3) R) (a b : Fin 3),
    adRep (r0 η Ψ) g X a b = ((Ψ g ^ wt a b : Rˣ) : R) * (if η g = 1 then X a b else -X b.rev a.rev) := by
  intro G R _ _ η Ψ g X a b
  have hR : (r0 η Ψ g).right = η g := rfl
  have hL : ((r0 η Ψ g).left : Matrix (Fin 3) (Fin 3) R) = diagonal fun i => ((Ψ g ^ wt1 i : Rˣ) : R) := by
    rw [unitaryThreeReflection_left, tor_val]
  have hLi : (((r0 η Ψ g).left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R)
      = diagonal fun i => (((Ψ g ^ wt1 i)⁻¹ : Rˣ) : R) := by
    rw [unitaryThreeReflection_left, ← map_inv, tor_val]
    simp only [_root_.inv_zpow]
  have e : adRep (r0 η Ψ) g X
      = (((r0 η Ψ g).left : Matrix (Fin 3) (Fin 3) R) * (if (r0 η Ψ g).right = 1 then X else thetaLie X))
        * (((r0 η Ψ g).left⁻¹ : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) := rfl
  rw [e, hR, hL, hLi, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hw : Ψ g ^ wt a b = Ψ g ^ wt1 a * (Ψ g ^ wt1 b)⁻¹ := by
    rw [wt, _root_.zpow_sub]
  rw [hw, Units.val_mul]
  split_ifs with h
  · ring
  · rw [theta_lie_apply]
    ring
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.Clifford
section
open Matrix UpperTheory.V.U3

private theorem common_eigen {κ E ι : Type*} [Field κ] [IsAlgClosed κ] [AddCommGroup E] [Module κ E]
    [FiniteDimensional κ E] (f : ι → Module.End κ E) (S : Submodule κ E) (hS : S ≠ ⊥)
    (hst : ∀ i, ∀ v ∈ S, f i v ∈ S) (hc : ∀ i j, ∀ v ∈ S, f i (f j v) = f j (f i v)) :
    ∃ v ∈ S, v ≠ 0 ∧ ∀ i, ∃ c : κ, f i v = c • v := by
  obtain ⟨F, ⟨hF0, hFS, hFst⟩, hmin⟩ := (wellFounded_lt (α := Submodule κ E)).has_min
    {F | F ≠ ⊥ ∧ F ≤ S ∧ ∀ i, ∀ v ∈ F, f i v ∈ F} ⟨S, hS, le_rfl, hst⟩
  obtain ⟨v, hvF, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hF0
  refine ⟨v, hFS hvF, hv0, fun i => ?_⟩
  haveI : Nontrivial F := Submodule.nontrivial_iff_ne_bot.mpr hF0
  obtain ⟨c, hc'⟩ := Module.End.exists_eigenvalue ((f i).restrict (hFst i) : Module.End κ F)
  obtain ⟨w, hw⟩ := hc'.exists_hasEigenvector
  have hw1 : f i w = c • (w : E) := congrArg Subtype.val hw.apply_eq_smul
  have hw0 : (w : E) ≠ 0 := fun h => hw.2 (Subtype.ext h)
  have key : ¬ F ⊓ Module.End.eigenspace (f i) c < F := by
    refine hmin _ ⟨?_, inf_le_left.trans hFS, ?_⟩
    · exact (Submodule.ne_bot_iff _).mpr ⟨w, ⟨w.2, Module.End.mem_eigenspace_iff.mpr hw1⟩, hw0⟩
    · rintro j u ⟨huF, hu⟩
      refine ⟨hFst j u huF, Module.End.mem_eigenspace_iff.mpr ?_⟩
      rw [hc i j u (hFS huF), Module.End.mem_eigenspace_iff.mp hu, map_smul]
  have h2 : F ⊓ Module.End.eigenspace (f i) c = F := (eq_or_lt_of_le inf_le_left).resolve_right key
  have : v ∈ F ⊓ Module.End.eigenspace (f i) c := by rw [h2]; exact hvF
  exact ⟨c, Module.End.mem_eigenspace_iff.mp this.2⟩

private theorem exists_compl {Γ κ V : Type*} [Group Γ] [Field κ] [AddCommGroup V] [Module κ V]
    [FiniteDimensional κ V] (σ : Γ →* Module.End κ V) (H : Subgroup Γ) [H.Normal]
    (hirr : ∀ W : Submodule κ V, (∀ g, ∀ v ∈ W, σ g v ∈ W) → W = ⊥ ∨ W = ⊤)
    (W₀ : Submodule κ V) (h0 : ∀ g ∈ H, ∀ v ∈ W₀, σ g v ∈ W₀) (hb : W₀ ≠ ⊥) (ht : W₀ ≠ ⊤) :
    ∃ U W : Submodule κ V, IsCompl U W ∧ U ≠ ⊥ ∧ W ≠ ⊥ ∧ (∀ g ∈ H, ∀ v ∈ U, σ g v ∈ U) ∧
      (∀ g ∈ H, ∀ v ∈ W, σ g v ∈ W) := by
  have hmul : ∀ a b v, σ a (σ b v) = σ (a * b) v := fun a b v => by rw [map_mul]; rfl
  have hcom : ∀ (X : Submodule κ V) (g : Γ), (∀ h ∈ H, ∀ v ∈ X, σ h v ∈ X) →
      ∀ h ∈ H, ∀ v ∈ X.comap (σ g), σ h v ∈ X.comap (σ g) := by
    intro X g hX h hh v hv
    have := hX (g * h * g⁻¹) (Subgroup.Normal.conj_mem h hh g) _ hv
    rw [hmul, inv_mul_cancel_right, ← hmul] at this
    exact this
  obtain ⟨W, ⟨hW0, hWst⟩, hmin⟩ := (wellFounded_lt (α := Submodule κ V)).has_min
    {F | F ≠ ⊥ ∧ ∀ g ∈ H, ∀ v ∈ F, σ g v ∈ F} ⟨W₀, hb, h0⟩
  obtain ⟨U, ⟨hU0, hUt, hUst⟩, hmax⟩ := (wellFounded_gt (α := Submodule κ V)).has_min
    {F | F ≠ ⊥ ∧ F ≠ ⊤ ∧ ∀ g ∈ H, ∀ v ∈ F, σ g v ∈ F} ⟨W₀, hb, ht, h0⟩
  have hex : ∃ g, ¬ W ≤ U.comap (σ g) := by
    by_contra hne
    push_neg at hne
    rcases hirr (⨅ g, U.comap (σ g)) (fun g v hv => by
      rw [Submodule.mem_iInf] at hv ⊢
      intro k
      have := hv (k * g)
      rw [Submodule.mem_comap, ← hmul] at this
      exact this) with h | h
    · exact hW0 (le_bot_iff.mp (h ▸ le_iInf hne))
    · apply hUt
      rw [eq_top_iff]
      intro v _
      have : v ∈ ⨅ g, U.comap (σ g) := by rw [h]; trivial
      simpa using (Submodule.mem_iInf _).mp this 1
  obtain ⟨g, hg⟩ := hex
  have hU' := hcom U g hUst
  have hback : ∀ u ∈ U, σ g⁻¹ u ∈ U.comap (σ g) := fun u hu => by
    rw [Submodule.mem_comap, hmul]; simpa using hu
  refine ⟨U.comap (σ g), W, ⟨?_, ?_⟩, ?_, hW0, hU', hWst⟩
  · rw [disjoint_iff]
    by_contra hne
    refine hmin _ ⟨hne, fun h hh v hv => ⟨hU' h hh v hv.1, hWst h hh v hv.2⟩⟩ ?_
    exact lt_of_le_of_ne inf_le_right fun h => hg (inf_eq_right.mp h)
  · rw [codisjoint_iff]
    by_contra hne
    have hX : ∀ h ∈ H, ∀ v ∈ U.comap (σ g) ⊔ W, σ h v ∈ U.comap (σ g) ⊔ W := by
      intro h hh v hv
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
      rw [map_add (f := _)]
      exact Submodule.add_mem_sup (hU' h hh a ha) (hWst h hh b hb)
    have hle : U ≤ (U.comap (σ g) ⊔ W).comap (σ g⁻¹) := fun u hu =>
      Submodule.mem_sup_left (hback u hu)
    refine hmax ((U.comap (σ g) ⊔ W).comap (σ g⁻¹)) ⟨?_, ?_, hcom _ _ hX⟩ ?_
    · exact fun h => hU0 (le_bot_iff.mp (h ▸ hle))
    · intro h
      apply hne
      rw [eq_top_iff]
      intro v _
      have : σ g v ∈ (U.comap (σ g) ⊔ W).comap (σ g⁻¹) := by rw [h]; trivial
      rw [Submodule.mem_comap, hmul] at this
      simpa using this
    · refine lt_of_le_of_ne hle fun h => hg fun w hw => ?_
      rw [Submodule.mem_comap, h, Submodule.mem_comap, hmul]
      simpa using Submodule.mem_sup_right hw
  · obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
    refine (Submodule.ne_bot_iff _).mpr ⟨_, hback u hu, fun h => hu0 ?_⟩
    have := congrArg (σ g) h
    rw [hmul] at this
    simpa using this

private theorem exists_traceless {Γ κ V : Type*} [Group Γ] [Field κ] [CharZero κ] [AddCommGroup V]
    [Module κ V] [FiniteDimensional κ V] (σ : Γ →* Module.End κ V) (H : Subgroup Γ)
    (U W : Submodule κ V) (hc : IsCompl U W) (hU0 : U ≠ ⊥) (hW0 : W ≠ ⊥)
    (hU : ∀ g ∈ H, ∀ v ∈ U, σ g v ∈ U) (hW : ∀ g ∈ H, ∀ v ∈ W, σ g v ∈ W) :
    ∃ P : Module.End κ V, P ≠ 0 ∧ LinearMap.trace κ V P = 0 ∧ ∀ h ∈ H, σ h * P = P * σ h := by
  let Q : Module.End κ V := U.subtype ∘ₗ U.linearProjOfIsCompl W hc
  have hQU : ∀ u ∈ U, Q u = u := fun u hu => by
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hc ⟨u, hu⟩)
  have hQW : ∀ u ∈ W, Q u = 0 := fun u hu => by
    exact congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_right hc ⟨u, hu⟩)
  have hQ : ∀ h ∈ H, σ h * Q = Q * σ h := by
    intro h hh
    ext v
    have : v ∈ U ⊔ W := by rw [hc.sup_eq_top]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp this
    simp [hQU a ha, hQW b hb, hQU _ (hU h hh a ha), hQW _ (hW h hh b hb)]
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
  obtain ⟨w, hw, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  haveI : Nontrivial V := ⟨u, 0, hu0⟩
  have hn : (Module.finrank κ V : κ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
  refine ⟨(Module.finrank κ V : κ) • Q - LinearMap.trace κ V Q • 1, fun h => ?_, ?_, ?_⟩
  · have h1 := congrArg (fun T : Module.End κ V => T w) h
    have h2 := congrArg (fun T : Module.End κ V => T u) h
    simp [hQW w hw, hw0] at h1
    simp [hQU u hu, h1, hu0] at h2
    exact hn (by simp [h2])
  · simp [mul_comm]
  · intro h hh
    simp [mul_sub, sub_mul, hQ h hh]

private theorem exists_twist {Γ κ V : Type*} [Group Γ] [Field κ] [IsAlgClosed κ] [CharZero κ]
    [AddCommGroup V] [Module κ V] [FiniteDimensional κ V] (σ : Γ →* Module.End κ V)
    (H : Subgroup Γ) [H.Normal] (hab : ∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ H)
    (P : Module.End κ V) (hP0 : P ≠ 0) (hPt : LinearMap.trace κ V P = 0)
    (hP : ∀ h ∈ H, σ h * P = P * σ h) :
    ∃ T : Module.End κ V, T ≠ 0 ∧ LinearMap.trace κ V T = 0 ∧ (∀ h ∈ H, σ h * T = T * σ h) ∧
      ∀ g, ∃ c : κ, σ g * T = c • (T * σ g) := by
  let S : Submodule κ (Module.End κ V) :=
    { carrier := {T | LinearMap.trace κ V T = 0 ∧ ∀ h ∈ H, σ h * T = T * σ h}
      add_mem' := fun ha hb => ⟨by simp [ha.1, hb.1], fun h hh => by
        rw [mul_add, add_mul, ha.2 h hh, hb.2 h hh]⟩
      zero_mem' := by simp
      smul_mem' := fun c a ha => ⟨by simp [ha.1], fun h hh => by simp [ha.2 h hh]⟩ }
  let f : Γ → Module.End κ (Module.End κ V) := fun g =>
    LinearMap.mulLeft κ (σ g) ∘ₗ LinearMap.mulRight κ (σ g⁻¹)
  have hf : ∀ g T, f g T = σ g * (T * σ g⁻¹) := fun _ _ => rfl
  have hff : ∀ a b T, f a (f b T) = f (a * b) T := fun a b T => by
    simp only [hf, _root_.mul_inv_rev, map_mul, mul_assoc]
  have hH : ∀ h ∈ H, ∀ T ∈ S, f h T = T := fun h hh T hT => by
    rw [hf, ← mul_assoc, hT.2 h hh, mul_assoc, ← map_mul]; simp
  have hst : ∀ g, ∀ T ∈ S, f g T ∈ S := by
    intro g T hT
    refine ⟨?_, fun h hh => ?_⟩
    · rw [hf, LinearMap.trace_mul_comm, mul_assoc, ← map_mul]; simpa using hT.1
    · have h1 := hT.2 (g⁻¹ * h * g) (by simpa using Subgroup.Normal.conj_mem h hh g⁻¹)
      have e1 : σ h * σ g = σ g * σ (g⁻¹ * h * g) := by
        rw [← map_mul, ← map_mul]; congr 1; group
      have e2 : σ g⁻¹ * σ h = σ (g⁻¹ * h * g) * σ g⁻¹ := by
        rw [← map_mul, ← map_mul]; congr 1; group
      rw [hf, ← mul_assoc, e1, mul_assoc, ← mul_assoc _ T, h1, mul_assoc, ← e2]
      simp only [mul_assoc]
  obtain ⟨T, hT, hT0, hTc⟩ := common_eigen f S ((Submodule.ne_bot_iff _).mpr ⟨P, ⟨hPt, hP⟩, hP0⟩) hst
    (fun a b T hT => by
      rw [← hH _ (hab a b) _ (hst b _ (hst a T hT)), hff, hff, hff]
      congr 2; group)
  refine ⟨T, hT0, hT.1, hT.2, fun g => ?_⟩
  obtain ⟨c, hc⟩ := hTc g
  refine ⟨c, ?_⟩
  rw [← smul_mul_assoc, ← hc, hf, mul_assoc, mul_assoc, ← map_mul]; simp

theorem UpperTheory.V.U3.exists_selfTwist :
    ∀ {Γ κ : Type} [Group Γ] [Field κ] [IsAlgClosed κ] [CharZero κ] {m : ℕ} (ρ : Γ →* GL (Fin m) κ) (H : Subgroup Γ) [H.Normal],
      (∀ a b : Γ, a * b * a⁻¹ * b⁻¹ ∈ H) → MatIrr ⊤ (fun g => (ρ g : Matrix (Fin m) (Fin m) κ)) → ¬ MatIrr H (fun g => (ρ g : Matrix (Fin m) (Fin m) κ)) →
      ∃ φ : Γ →* κˣ, φ ≠ 1 ∧ H ≤ φ.ker ∧ φ ^ m = 1 ∧
        MatIso ⊤ (fun g => ((φ g : κˣ) : κ) • (ρ g : Matrix (Fin m) (Fin m) κ)) (fun g => (ρ g : Matrix (Fin m) (Fin m) κ)) := by
  intro Γ κ _ _ _ _ m ρ H _ hab hirr hred
  let σ : Γ →* Module.End κ (Fin m → κ) :=
    { toFun := fun g => Matrix.toLin' (ρ g : Matrix (Fin m) (Fin m) κ)
      map_one' := by simp [Module.End.one_eq_id]
      map_mul' := fun a b => by simp [Matrix.toLin'_mul, Module.End.mul_eq_comp] }
  have hσ : ∀ g v, σ g v = (ρ g : Matrix (Fin m) (Fin m) κ) *ᵥ v := fun g v => Matrix.toLin'_apply _ _
  have hirr' : ∀ W : Submodule κ (Fin m → κ), (∀ g, ∀ v ∈ W, σ g v ∈ W) → W = ⊥ ∨ W = ⊤ :=
    fun W hW => hirr W fun g _ v hv => hσ g v ▸ hW g v hv
  unfold MatIrr at hred
  push_neg at hred
  obtain ⟨W₀, h0, hb, ht⟩ := hred
  obtain ⟨U, W, hc, hU0, hW0, hU, hW⟩ := exists_compl σ H hirr' W₀
    (fun g hg v hv => by rw [hσ]; exact h0 g hg v hv) hb ht
  obtain ⟨P, hP0, hPt, hP⟩ := exists_traceless σ H U W hc hU0 hW0 hU hW
  obtain ⟨T, hT0, hTt, hTH, hT⟩ := exists_twist σ H hab P hP0 hPt hP
  choose c hc using hT
  have hunit : ∀ g, IsUnit (σ g) := fun g => (Group.isUnit g).map σ
  have hne : ∀ g, T * σ g ≠ 0 := fun g h => hT0 ((hunit g).mul_left_eq_zero.mp h)
  have hc0 : ∀ g, c g ≠ 0 := fun g h => hT0 ((hunit g).mul_right_eq_zero.mp (by rw [hc, h, zero_smul]))
  have huniq : ∀ g d, σ g * T = d • (T * σ g) → c g = d := fun g d h =>
    smul_left_injective κ (hne g) ((hc g).symm.trans h)
  let φ : Γ →* κˣ :=
    { toFun := fun g => Units.mk0 (c g) (hc0 g)
      map_one' := Units.ext (huniq 1 1 (by simp))
      map_mul' := fun a b => Units.ext (huniq _ _ (by
        rw [map_mul, mul_assoc, hc b, mul_smul_comm, ← mul_assoc, hc a, smul_mul_assoc, smul_smul,
          mul_assoc, mul_comm (c b)]
        rfl)) }
  have hφ : ∀ g, (φ g : κ) = c g := fun _ => rfl
  have hker : LinearMap.ker T = ⊥ := by
    refine (hirr' _ fun g v hv => ?_).resolve_right fun h => hT0 (LinearMap.ker_eq_top.mp h)
    have := congrArg (fun A : Module.End κ (Fin m → κ) => A v) (hc g)
    simp only [Module.End.mul_apply, LinearMap.smul_apply, LinearMap.mem_ker.mp hv, map_zero] at this
    exact (smul_eq_zero.mp this.symm).resolve_left (hc0 g)
  have hTu : IsUnit T := (LinearMap.isUnit_iff_ker_eq_bot T).mpr hker
  have hdet : (LinearMap.toMatrix' T).det ≠ 0 := by
    rw [LinearMap.det_toMatrix']
    exact (hTu.map LinearMap.det).ne_zero
  have hM : ∀ g, LinearMap.toMatrix' T * (c g • (ρ g : Matrix (Fin m) (Fin m) κ)) =
      (ρ g : Matrix (Fin m) (Fin m) κ) * LinearMap.toMatrix' T := fun g => by
    have := congrArg LinearMap.toMatrix' (hc g)
    rw [map_smul, LinearMap.toMatrix'_mul, LinearMap.toMatrix'_mul] at this
    simpa [σ] using this.symm
  refine ⟨φ, fun h1 => ?_, fun h hh => ?_, ?_, ⟨GeneralLinearGroup.mkOfDetNeZero _ hdet, fun g _ => hM g⟩⟩
  · haveI : Nontrivial (Fin m → κ) := by
      obtain ⟨u, -, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hU0
      exact ⟨u, 0, hu0⟩
    obtain ⟨a, ha⟩ := Module.End.exists_eigenvalue T
    have htop : Module.End.eigenspace T a = ⊤ := by
      refine (hirr' _ fun g v hv => ?_).resolve_left ha
      have := congrArg (fun A : Module.End κ (Fin m → κ) => A v) (hc g)
      rw [Module.End.mem_eigenspace_iff] at hv ⊢
      simp only [Module.End.mul_apply, LinearMap.smul_apply, hv, map_smul, ← hφ, h1] at this
      simpa using this.symm
    have hTa : T = a • 1 := by
      refine LinearMap.ext fun v => ?_
      exact Module.End.mem_eigenspace_iff.mp (by rw [htop]; trivial)
    have hn : (Module.finrank κ (Fin m → κ) : κ) ≠ 0 := Nat.cast_ne_zero.mpr Module.finrank_pos.ne'
    rw [hTa, map_smul, LinearMap.trace_one, smul_eq_mul, mul_eq_zero] at hTt
    exact hT0 (by rw [hTa, hTt.resolve_right hn, zero_smul])
  · exact Units.ext (huniq h 1 (by rw [one_smul, hTH h hh]))
  · ext g
    have := congrArg Matrix.det (hM g)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_smul, mul_comm _ (LinearMap.toMatrix' T).det] at this
    have h2 := mul_left_cancel₀ hdet this
    have h3 : (ρ g : Matrix (Fin m) (Fin m) κ).det ≠ 0 := (ρ g).det_ne_zero
    simpa [hφ, h3] using h2
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ConjTor
section
open Matrix UpperTheory.V.U3

private theorem sgnAct_tor {R : Type} [CommRing R] (s : ℤˣ) (t : Rˣ) :
    sgnAct (m := 3) (R := R) s (tor R t) = tor R t := by
  rcases Int.units_eq_one_or s with rfl | rfl <;> simp [theta_tor]

private theorem conj_left {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (t : Rˣ) (g : G) :
    (conjBy (tor R t) r g).left = tor R t * (r g).left * tor R t⁻¹ := by
  simp [conjBy, MulAut.conj_apply, SemidirectProduct.mul_left, SemidirectProduct.inv_left, sgnAct_tor, map_inv]

private theorem conj_right {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (t : Rˣ) (g : G) :
    (conjBy (tor R t) r g).right = (r g).right := by
  simp [conjBy, MulAut.conj_apply, SemidirectProduct.mul_right, SemidirectProduct.inv_right]

private theorem conj_mat {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (t : Rˣ) (g : G)
    (a b : Fin 3) :
    (conjBy (tor R t) r g).mat a b = ((t ^ wt a b : Rˣ) : R) * (r g).mat a b := by
  show (((conjBy (tor R t) r g).left : GL (Fin 3) R) : Matrix (Fin 3) (Fin 3) R) a b = _
  rw [conj_left, Units.val_mul, Units.val_mul, tor_val, tor_val, mul_diagonal, diagonal_mul]
  have key : ((t ^ wt1 a : Rˣ) : R) * ((t⁻¹ ^ wt1 b : Rˣ) : R) = ((t ^ wt a b : Rˣ) : R) := by
    rw [← Units.val_mul, wt, _root_.zpow_sub, _root_.inv_zpow]
  rw [← key, GG.mat]
  ring

private theorem conj_zmat {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (t : Rˣ) (c g₁ : G)
    (a b : Fin 3) :
    zmat c g₁ (conjBy (tor R t) r) a b = ((t ^ wt a b : Rˣ) : R) * zmat c g₁ r a b := by
  simp only [zmat, Matrix.sub_apply, conj_mat, mul_sub]

theorem UpperTheory.V.U3.conjBy_tor :
    ∀ {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (t : Rˣ),
    (∀ g a b, (conjBy (tor R t) r g).mat a b = ((t ^ wt a b : Rˣ) : R) * (r g).mat a b) ∧ (∀ g, (conjBy (tor R t) r g).right = (r g).right) ∧
    (∀ c g₁, Normalised c g₁ r → Normalised c g₁ (conjBy (tor R t) r)) ∧ (∀ c g₁, zeta c g₁ (conjBy (tor R t) r) = zeta c g₁ r) ∧
    ∀ (η : G →* ℤˣ) (Ψ : G →* Rˣ), conjBy (tor R t) (r0 η Ψ) = r0 η Ψ := by
  intro G R _ _ r t
  refine ⟨conj_mat r t, conj_right r t, ?_, ?_, ?_⟩
  · intro c g₁ h
    refine ⟨?_, ?_, ?_⟩
    · ext a b
      rw [conj_mat, h.atc]
      by_cases hab : a = b
      · subst hab
        simp [wt]
      · simp [Matrix.one_apply_ne hab]
    · rw [conj_zmat, h.z12, mul_zero]
    · rw [conj_zmat, h.z21, mul_zero]
  · intro c g₁
    unfold zeta
    rw [conj_zmat]
    simp [wt]
  · intro η Ψ
    refine MonoidHom.ext fun g => ?_
    refine SemidirectProduct.ext ?_ (conj_right _ t g)
    rw [conj_left, unitaryThreeReflection_left, ← map_mul, ← map_mul, mul_inv_cancel_comm]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.ConjugateStarMatrix
section
open Matrix UpperTheory.V.U3

private theorem conjugate_star_matrix {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (c g : G)
    (hc : (r c).right = -1) (hg : (r g).right = 1) (hm : (r c).mat = 1) :
    (r (gstar c g)).mat = Jmat (R := R) 3 * (r g).matᵀ * Jmat (R := R) 3 := by
  have hc' : r c = SemidirectProduct.mk 1 (-1) := by
    apply SemidirectProduct.ext
    · exact Units.ext (by simpa [GG.mat] using hm)
    · exact hc
  have hg' : r g = SemidirectProduct.mk (r g).left 1 := SemidirectProduct.ext rfl hg
  have hs : r (gstar c g) = r c * (r g)⁻¹ * r c := by
    simp only [gstar, map_mul, map_inv]
  rw [hs, hc', hg']
  simp only [GG.mat, SemidirectProduct.mul_left, SemidirectProduct.mul_right, SemidirectProduct.inv_left,
    SemidirectProduct.inv_right, inv_one, map_one, mul_one, one_mul, MulAut.one_apply, map_inv,
    sgnAct_neg_one, theta_inv_val]

theorem UpperTheory.V.U3.zmat_diag :
    ∀ {G R : Type} [Group G] [CommRing R] (r : G →* GG (m := 3) (R := R)) (c g₁ : G), IsUnit (2 : R) → (r c).right = -1 → (r g₁).right = 1 → Normalised c g₁ r →
    zmat c g₁ r = Matrix.diagonal ![zeta c g₁ r, 0, -zeta c g₁ r] := by
  intro G R _ _ r c g₁ _ hc hg hN
  have hJ : ∀ (M : Matrix (Fin 3) (Fin 3) R) (i j : Fin 3), (Jmat (R := R) 3 * Mᵀ * Jmat (R := R) 3) i j = M j.rev i.rev := by
    intro M i j
    simp only [Matrix.mul_apply, Jmat, Matrix.transpose_apply, ite_mul, mul_ite, one_mul, zero_mul, mul_zero,
      Finset.sum_ite_eq', Finset.sum_ite_eq, Finset.mem_univ, if_true]
    rw [Finset.sum_eq_single j.rev]
    · simp
    · intro x _ hx
      rw [if_neg]
      intro h
      exact hx (by rw [h, Fin.rev_rev])
    · simp
  have hZ : ∀ i j : Fin 3, zmat c g₁ r i j = (r g₁).mat i j - (r g₁).mat j.rev i.rev := by
    intro i j
    simp only [zmat, Matrix.sub_apply]
    rw [conjugate_star_matrix r c g₁ hc hg hN.atc, hJ]
  have h01 := hN.z12
  have h10 := hN.z21
  rw [hZ] at h01 h10
  have e0 : (0 : Fin 3).rev = 2 := rfl
  have e1 : (1 : Fin 3).rev = 1 := rfl
  have e2 : (2 : Fin 3).rev = 0 := rfl
  rw [e0, e1] at h01 h10
  ext i j
  simp only [zeta]
  rw [hZ, hZ 0 0, e0]
  fin_cases i <;> fin_cases j <;> simp [e0, e1, e2, Matrix.diagonal] <;>
    first
    | linear_combination h01
    | linear_combination -h01
    | linear_combination h10
    | linear_combination -h10
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DefCob
section
open Matrix UpperTheory.V.U3

private theorem UpperTheory.V.U3.defcob_mul_zero {C : Type} [CommRing C] {m : ℕ} {I : Ideal C}
    (hI : I * I = ⊥) {X Y : Matrix (Fin m) (Fin m) C} (hX : EntIn I X) (hY : EntIn I Y)
    (A : Matrix (Fin m) (Fin m) C) : X * A * Y = 0 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.zero_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  have h1 : (X * A) i k ∈ I := by
    rw [Matrix.mul_apply]
    exact I.sum_mem fun l _ => I.mul_mem_right _ (hX i l)
  have h2 := Ideal.mul_mem_mul h1 (hY k j)
  rw [hI] at h2
  exact h2

private theorem UpperTheory.V.U3.defcob_entIn {C : Type} [CommRing C] {m : ℕ} {I : Ideal C}
    {X : Matrix (Fin m) (Fin m) C} (hX : EntIn I X)
    (A B : Matrix (Fin m) (Fin m) C) : EntIn I (A * Xᵀ * B) := by
  intro i j
  rw [Matrix.mul_apply]
  refine I.sum_mem fun k _ => I.mul_mem_right _ ?_
  rw [Matrix.mul_apply]
  exact I.sum_mem fun l _ => I.mul_mem_left _ (hX k l)

theorem UpperTheory.V.U3.isDeform_cob :
    ∀ {G C : Type} [Group G] [CommRing C] {m : ℕ} (I : Ideal C)
      (r : G →* GG (m := m) (R := C)) (X : Matrix (Fin m) (Fin m) C), I * I = ⊥ → EntIn I X →
      ∃ h : GL (Fin m) C, (h : Matrix (Fin m) (Fin m) C) = 1 + X ∧ IsDeform r (cob r X) (conjBy h r) := by
  intro G C _ _ m I r X hI hX
  have hXX : X * X = 0 := by simpa using defcob_mul_zero hI hX hX 1
  let h : GL (Fin m) C := ⟨1 + X, 1 - X, by
    rw [Matrix.mul_sub, Matrix.add_mul, Matrix.add_mul, hXX]; simp, by
    rw [Matrix.mul_add, Matrix.sub_mul, Matrix.sub_mul, hXX]; simp⟩
  have hv : (h : Matrix (Fin m) (Fin m) C) = 1 + X := rfl
  have hi : ((h⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) = 1 - X := rfl
  refine ⟨h, rfl, fun g => ⟨by simp [conjBy], ?_⟩⟩
  have hl : (conjBy h r g).mat = (1 + X) * (r g).mat *
      ((sgnAct (m := m) (R := C) (r g).right h⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) := by
    simp [conjBy, GG.mat, hv]
  have hc : cob r X g = X - (r g).adFun X := rfl
  have ha : (((r g).left⁻¹ : GL (Fin m) C) : Matrix (Fin m) (Fin m) C) * (r g).mat = 1 :=
    Units.inv_mul _
  rw [hl, hc, GG.adFun]
  rcases Int.units_eq_one_or (r g).right with hs | hs
  · rw [hs, sgnAct_one, hi, ite_eq_left rfl]
    simp only [Matrix.mul_sub, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one]
    rw [defcob_mul_zero hI hX hX, Matrix.mul_assoc _ _ (r g).mat, ha, Matrix.mul_one]
    abel
  · have hJ : Jmat (R := C) m * (1 + X)ᵀ * Jmat (R := C) m =
        1 + Jmat (R := C) m * Xᵀ * Jmat (R := C) m := by
      rw [Matrix.transpose_add, Matrix.transpose_one, Matrix.mul_add, Matrix.add_mul,
        Matrix.mul_one, Jmat_mul_Jmat]
    rw [hs, sgnAct_neg_one, theta_val, inv_inv, hv, hJ, ite_eq_right (by decide), thetaLie]
    simp only [Matrix.mul_add, Matrix.add_mul, Matrix.sub_mul, Matrix.one_mul, Matrix.mul_one]
    rw [defcob_mul_zero hI hX (defcob_entIn hX _ _), Matrix.mul_assoc _ _ (r g).mat, ha,
      Matrix.mul_one, Matrix.mul_neg]
    abel
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.UnitaryThreeGroups.DefNorm
section
open Matrix UpperTheory.V.U3

theorem UpperTheory.V.U3.isDeform_normalised_iff :
    ∀ {G C : Type} [Group G] [CommRing C] (r r' : G →* GG (m := 3) (R := C))
      (γ : G → Matrix (Fin 3) (Fin 3) C) (c g₁ : G),
      Normalised c g₁ r → IsDeform r γ r' → (Normalised c g₁ r' ↔ NormCoc c g₁ r γ) := by
  intro G C _ _ r r' γ c g₁ hn hd
  have hc : (r' c).mat = 1 + γ c := by rw [(hd c).2, hn.atc, Matrix.mul_one]
  have hz : zmat c g₁ r' = zmat c g₁ r + zvar c g₁ r γ := by
    simp only [zmat, zvar, (hd _).2, Matrix.add_mul, Matrix.one_mul]
    abel
  have h12 : zmat c g₁ r' 0 1 = zvar c g₁ r γ 0 1 := by
    rw [hz, Matrix.add_apply, hn.z12, zero_add]
  have h21 : zmat c g₁ r' 1 0 = zvar c g₁ r γ 1 0 := by
    rw [hz, Matrix.add_apply, hn.z21, zero_add]
  constructor
  · intro h
    refine ⟨?_, h12 ▸ h.z12, h21 ▸ h.z21⟩
    have := h.atc
    rw [hc] at this
    exact add_eq_left.mp this
  · intro h
    exact ⟨by rw [hc, h.atc, add_zero], h12.trans h.z12, h21.trans h.z21⟩
end

