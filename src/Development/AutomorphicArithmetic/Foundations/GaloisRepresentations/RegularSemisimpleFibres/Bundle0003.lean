module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0104

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PJdIso
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section Transport

variable {F F' : Type} [Field F] [Field F'] (r : F ≃+* F')

private theorem coe_phi {n : ℕ} (x : GL (Fin n) F) :
    ((Matrix.GeneralLinearGroup.map r.toRingHom x : GL (Fin n) F') : Matrix (Fin n) (Fin n) F') =
      (x : Matrix (Fin n) (Fin n) F).map r := by
  ext i j
  simp [Matrix.GeneralLinearGroup.map_apply]

private def phiE (n : ℕ) : GL (Fin n) F ≃ GL (Fin n) F' where
  toFun := Matrix.GeneralLinearGroup.map r.toRingHom
  invFun := Matrix.GeneralLinearGroup.map r.symm.toRingHom
  left_inv x := by
    apply Units.ext
    ext i j
    simp [Matrix.GeneralLinearGroup.map_apply]
  right_inv x := by
    apply Units.ext
    ext i j
    simp [Matrix.GeneralLinearGroup.map_apply]

private theorem inPar_phi (a : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    InPar a (Matrix.GeneralLinearGroup.map r.toRingHom x) ↔ InPar a x := by
  unfold InPar
  simp only [coe_phi, Matrix.map_apply]
  constructor
  · intro h i j hj hi
    exact (map_eq_zero_iff r r.injective).1 (h i j hj hi)
  · intro h i j hj hi
    rw [h i j hj hi, map_zero]

private theorem ent_map {n : ℕ} (M : Matrix (Fin n) (Fin n) F) (i j : ℕ) :
    ent (M.map r) i j = r (ent M i j) := by
  unfold ent
  split_ifs
  · rfl
  · exact (map_zero r).symm

private theorem tl_map (a : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    tl a (M.map r) = (tl a M).map r := by
  ext i j
  simp [tl, ent_map]

private theorem br_map (a b : ℕ) {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    br a b (M.map r) = (br a b M).map r := by
  ext i j
  simp [br, ent_map]

private theorem isUnit_map {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    IsUnit (M.map r) ↔ IsUnit M := by
  have := isUnit_map_iff (r.mapMatrix (m := Fin n)) M
  simpa [RingEquiv.mapMatrix_apply] using this

private theorem coe_toG {n : ℕ} {M : Matrix (Fin n) (Fin n) F} (h : IsUnit M) :
    ((toG M : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = M := by
  unfold toG
  rw [dite_eq_left h]
  rfl

private theorem toG_map {n : ℕ} (M : Matrix (Fin n) (Fin n) F) :
    toG (M.map r) = Matrix.GeneralLinearGroup.map r.toRingHom (toG M) := by
  by_cases h : IsUnit M
  · apply Units.ext
    rw [coe_toG ((isUnit_map r M).2 h), coe_phi, coe_toG h]
  · have h' : ¬ IsUnit (M.map r) := fun k => h ((isUnit_map r M).1 k)
    unfold toG
    rw [dite_eq_right h, dite_eq_right h', map_one]

private theorem tlG_phi (a : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    tlG a (Matrix.GeneralLinearGroup.map r.toRingHom x) =
      Matrix.GeneralLinearGroup.map r.toRingHom (tlG a x) := by
  unfold tlG
  rw [coe_phi, tl_map, toG_map]

private theorem brG_phi (a b : ℕ) {n : ℕ} (x : GL (Fin n) F) :
    brG a b (Matrix.GeneralLinearGroup.map r.toRingHom x) =
      Matrix.GeneralLinearGroup.map r.toRingHom (brG a b x) := by
  unfold brG
  rw [coe_phi, br_map, toG_map]

include r in
private theorem card_phi (a n : ℕ) :
    Nat.card {p : GL (Fin n) F' // InPar a p} = Nat.card {p : GL (Fin n) F // InPar a p} :=
  (Nat.card_congr ((phiE r n).subtypeEquiv fun x => (inPar_phi r a x).symm)).symm

private theorem gal_id {K : Type} [Field K] (n : ℕ) (y : GL (Fin n) K) : gal (RingHom.id K) n y = y := by
  apply Units.ext
  ext i j
  simp [gal, Matrix.GeneralLinearGroup.map_apply]

private theorem hc_phi (a b : ℕ) (α : GL (Fin a) F' → ℂ) (β : GL (Fin b) F' → ℂ) (n : ℕ)
    (g : GL (Fin n) F) :
    hc a b α β n (Matrix.GeneralLinearGroup.map r.toRingHom g) =
      hc a b (fun x => α (Matrix.GeneralLinearGroup.map r.toRingHom x))
        (fun x => β (Matrix.GeneralLinearGroup.map r.toRingHom x)) n g := by
  unfold hc hcTw
  simp only [gal_id]
  rw [card_phi r a n, ← finsum_comp_equiv (phiE r n)]
  congr 1
  refine finsum_congr fun y => ?_
  have e : (phiE r n y)⁻¹ * Matrix.GeneralLinearGroup.map r.toRingHom g * phiE r n y =
      Matrix.GeneralLinearGroup.map r.toRingHom (y⁻¹ * g * y) := by
    simp only [map_mul, map_inv]
    rfl
  rw [e]
  simp only [inPar_phi, tlG_phi, brG_phi]

private theorem detc_phi (j : AlgebraicClosure F ≃+* AlgebraicClosure F')
    (hj : ∀ x, j (algebraMap _ _ x) = algebraMap _ _ (r x)) (θ : AlgebraicClosure F' →* ℂ)
    (t k : ℕ) (x : GL (Fin t) F) :
    detc θ t k (Matrix.GeneralLinearGroup.map r.toRingHom x) = detc (θ.comp j.toMonoidHom) t k x := by
  unfold detc
  have e : ((x : Matrix (Fin t) (Fin t) F).map r).det = r (x : Matrix (Fin t) (Fin t) F).det :=
    (RingHom.map_det r.toRingHom _).symm
  rw [coe_phi, e, ← hj]
  rfl

end Transport

theorem UpperTheory.Gal.InertialTypesAlt.jdIso :
    CuspIso → JDIso := by
  intro hC F F' _ _ _ r j hj θ D L n g
  have hJ : ∀ (L : List (ℕ × ℕ)) (n : ℕ) (g : GL (Fin n) F),
      J θ L n (Matrix.GeneralLinearGroup.map r.toRingHom g) = J (θ.comp j.toMonoidHom) L n g := by
    intro L
    induction L with
    | nil => intro n g; rfl
    | cons p L ih =>
      intro n g
      rw [J_cons, J_cons, hc_phi]
      congr 1
      · funext x
        exact hC F F' r j hj θ p.1 p.2 x
      · funext x
        exact ih _ x
  induction D generalizing n g with
  | nil => exact hJ L n g
  | cons p D ih =>
    rw [JD_cons, JD_cons, hc_phi]
    congr 1
    · funext x
      exact detc_phi r j hj θ p.1 p.2 x
    · funext x
      exact ih _ x
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PLblIso
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

section SlopeTestRemainingChoices

open GlobalTheory.Parabolic (mem_fixed)

variable {k K : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]

private def intEquiv (i : k ≃+* K) (hi : ∀ x : k, valuation K (i x) ≤ 1 ↔ valuation k x ≤ 1) : 𝒪[k] ≃+* 𝒪[K] where
  toFun x := ⟨i x, (hi x).2 x.2⟩
  invFun y := ⟨i.symm y, (hi _).1 (by rw [i.apply_symm_apply]; exact y.2)⟩
  left_inv x := Subtype.ext (by simp)
  right_inv y := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp)
  map_add' x y := Subtype.ext (by simp)

private def resEquiv (i₀ : 𝒪[k] ≃+* 𝒪[K]) : 𝓀[k] ≃+* 𝓀[K] := IsLocalRing.ResidueField.mapEquiv i₀

private def glEquiv {F F' : Type} [Field F] [Field F'] (r : F ≃+* F') (n : ℕ) : GL (Fin n) F ≃ GL (Fin n) F' where
  toFun := Matrix.GeneralLinearGroup.map r.toRingHom
  invFun := Matrix.GeneralLinearGroup.map r.symm.toRingHom
  left_inv g := by ext a b; simp
  right_inv g := by ext a b; simp

variable (i : k ≃+* K) (hi : ∀ x : k, valuation K (i x) ≤ 1 ↔ valuation k x ≤ 1) {n : ℕ}

include hi

private theorem map_alg (u : GL (Fin n) 𝒪[k]) :
    Matrix.GeneralLinearGroup.map i.toRingHom (Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) u) =
      Matrix.GeneralLinearGroup.map (algebraMap 𝒪[K] K)
        (Matrix.GeneralLinearGroup.map (intEquiv i hi).toRingHom u) := by
  ext a b; rfl

private theorem map_mem_KO {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) :
    Matrix.GeneralLinearGroup.map i.toRingHom g ∈ KO K (Fin n) := by
  obtain ⟨u, rfl⟩ := hg
  exact ⟨_, (map_alg i hi u).symm⟩

private theorem exists_KO {y : GL (Fin n) K} (hy : y ∈ KO K (Fin n)) :
    ∃ g ∈ KO k (Fin n), Matrix.GeneralLinearGroup.map i.toRingHom g = y := by
  obtain ⟨u, rfl⟩ := hy
  refine ⟨_, ⟨Matrix.GeneralLinearGroup.map (intEquiv i hi).symm.toRingHom u, rfl⟩, ?_⟩
  rw [map_alg i hi]
  congr 1
  ext a b
  simp

private theorem red_map (g : KO k (Fin n)) :
    redK K (Fin n) ⟨Matrix.GeneralLinearGroup.map i.toRingHom g, map_mem_KO i hi g.2⟩ =
      Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).toRingHom (redK k (Fin n) g) := by
  ext a b
  rw [redK_apply]
  show _ = resEquiv (intEquiv i hi) ((redK k (Fin n) g : Matrix (Fin n) (Fin n) 𝓀[k]) a b)
  rw [redK_apply]
  rfl

private theorem map_mem_KOne_iff {g : GL (Fin n) k} (hg : g ∈ KO k (Fin n)) :
    Matrix.GeneralLinearGroup.map i.toRingHom g ∈ KOne K (Fin n) ↔ g ∈ KOne k (Fin n) := by
  rw [← redK_eq_one_iff ⟨g, hg⟩, ← redK_eq_one_iff ⟨_, map_mem_KO i hi hg⟩, red_map i hi ⟨g, hg⟩]
  constructor
  · intro h
    have := congrArg (glEquiv (resEquiv (intEquiv i hi)) n).symm h
    rw [show Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).toRingHom (redK k (Fin n) ⟨g, hg⟩) =
      glEquiv (resEquiv (intEquiv i hi)) n (redK k (Fin n) ⟨g, hg⟩) from rfl, Equiv.symm_apply_apply] at this
    rw [this]
    exact map_one (Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).symm.toRingHom)
  · intro h
    rw [h, map_one]

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  (π : Representation ℂ (GL (Fin n) k) V) (P : Representation ℂ (GL (Fin n) K) W) (e : V ≃ₗ[ℂ] W)
  (he : ∀ g x, e (π g x) = P (Matrix.GeneralLinearGroup.map i.toRingHom g) (e x))

include he in
private theorem map_fixed :
    (fixed π (KOne k (Fin n))).map (e : V →ₗ[ℂ] W) = fixed P (KOne K (Fin n)) := by
  ext w
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine mem_fixed.2 fun y hy => ?_
    obtain ⟨g, hg, rfl⟩ := exists_KO i hi (GlobalTheory.StepData.KOne_le_KO hy)
    show P _ (e x) = e x
    rw [← he, mem_fixed.1 hx g ((map_mem_KOne_iff i hi hg).1 hy)]
  · intro hw
    refine ⟨e.symm w, mem_fixed.2 fun g hg => ?_, by simp⟩
    apply e.injective
    rw [he, e.apply_symm_apply,
      mem_fixed.1 hw _ ((map_mem_KOne_iff i hi (GlobalTheory.StepData.KOne_le_KO hg)).2 hg)]

private def fixEquiv : fixed π (KOne k (Fin n)) ≃ₗ[ℂ] fixed P (KOne K (Fin n)) :=
  e.ofSubmodules _ _ (map_fixed i hi π P e he)

private theorem fixEquiv_level (γ : GL (Fin n) 𝓀[k]) (x : fixed π (KOne k (Fin n))) :
    fixEquiv i hi π P e he (levelZero π γ x) =
      levelZero P (Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).toRingHom γ)
        (fixEquiv i hi π P e he x) := by
  obtain ⟨g, rfl⟩ := redK_surjective γ
  rw [← red_map i hi g]
  apply Subtype.ext
  rw [levelZero_apply]
  show e (levelZero π (redK k (Fin n) g) x : V) = P _ (e x)
  rw [levelZero_apply, he]

include he in
private theorem trace_level (γ : GL (Fin n) 𝓀[k]) :
    LinearMap.trace ℂ _ (levelZero P (Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).toRingHom γ)) =
      LinearMap.trace ℂ _ (levelZero π γ) := by
  have h : levelZero P (Matrix.GeneralLinearGroup.map (resEquiv (intEquiv i hi)).toRingHom γ) =
      (fixEquiv i hi π P e he).conj (levelZero π γ) := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := (fixEquiv i hi π P e he).surjective x
    rw [LinearEquiv.conj_apply_apply, LinearEquiv.symm_apply_apply, fixEquiv_level]
  rw [h, LinearMap.trace_conj']

end SlopeTestRemainingChoices

theorem UpperTheory.Gal.InertialTypesAlt.lblIso :
    JDIso → LblIso := by
  intro hJ k _ _ _ _ K _ _ _ _ i hi j hj θ N V W _ _ _ _ π P e he a ha
  obtain ⟨hok, hq, hn, hm⟩ := ha
  have hjr : ∀ x, j (algebraMap _ _ x) = algebraMap _ _ (resEquiv (intEquiv i hi) x) := by
    intro x
    obtain ⟨y, rfl⟩ := IsLocalRing.residue_surjective x
    exact hj y (intEquiv i hi y) rfl
  refine ⟨hok, hq.trans (Nat.card_congr (resEquiv (intEquiv i hi)).toEquiv), hn, ?_⟩
  unfold Meets at hm ⊢
  rw [← finsum_comp_equiv (glEquiv (resEquiv (intEquiv i hi)) N)]
  have key : ∀ γ : GL (Fin N) 𝓀[k],
      star (JD θ a.D a.L N (glEquiv (resEquiv (intEquiv i hi)) N γ)) *
          LinearMap.trace ℂ _ (levelZero P (glEquiv (resEquiv (intEquiv i hi)) N γ)) =
        star (JD (θ.comp j.toMonoidHom) a.D a.L N γ) * LinearMap.trace ℂ _ (levelZero π γ) := by
    intro γ
    rw [← hJ _ _ (resEquiv (intEquiv i hi)) j hjr θ a.D a.L N γ, ← trace_level i hi π P e he γ]
    rfl
  rw [finsum_congr key]
  exact hm
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PLblOf
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem isCl_trace {G W : Type} [Group G] [AddCommGroup W] [Module ℂ W]
    (ρ : Representation ℂ G W) : IsCl fun g => LinearMap.trace ℂ W (ρ g) := by
  intro x y
  show LinearMap.trace ℂ W (ρ (y⁻¹ * x * y)) = LinearMap.trace ℂ W (ρ x)
  rw [map_mul ρ, map_mul ρ, LinearMap.trace_mul_comm, ← mul_assoc, ← map_mul ρ, mul_inv_cancel,
    map_one, one_mul]

theorem UpperTheory.Gal.InertialTypesAlt.lblOf :
    MeetsIff → FrobL → JDEq → CuspChar → TensTr → CuspIrr → TensFix → SubqMap → SuppStd → LblOf := by
  intro hM hF hJ hC hT hCI hTF hSQ hSS k _ _ _ _ _ θ hθ N V _ _ π S hS hfix
  obtain ⟨s, x, hd, hmap, hsub⟩ := hSS k N V π S hS
  have hmem : ∀ a, x a ∈ S := fun a => by
    rw [← hmap]
    exact Multiset.mem_map_of_mem _ (Finset.mem_univ_val a)
  have hcusp : ∀ a, (x a).IsCusp := fun a => hS.isCusp (hmem a)
  have hdz : ∀ y ∈ S, UpperTheory.Zero.LLC.DZ y := by
    obtain ⟨h, x', hx', hcs⟩ := id hS
    intro y hy
    rw [← hx'] at hy
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hy
    have hv : ∃ v ∈ fixed π (KOne k (Fin N)), v ≠ 0 := Submodule.exists_mem_ne_zero_of_ne_bot hfix
    obtain ⟨v, hv, hv0⟩ := UpperTheory.Zero.LLC.Pr.dzs k N ⟨V, π, hS.isSmooth, hS.isIrreducible⟩ h
      (fun a => (x' a).fst)
      (fun a => ⟨(x' a).snd.rep.V, (x' a).rep, (x' a).snd.rep.smooth, (x' a).snd.rep.irr⟩) hcs hv a
    exact (Submodule.ne_bot_iff _).2 ⟨v, hv, hv0⟩
  have hdzx : ∀ a, UpperTheory.Zero.LLC.DZ (x a) := fun a => hdz _ (hmem a)
  have hci := fun a => hCI k (x a) (hcusp a) (hdzx a)
  have hch : ∀ a, ∃ j, Reg (Nat.card 𝓀[k]) (x a).fst j ∧
      ∀ γ, LinearMap.trace ℂ _ (levelZero (x a).rep γ) = cusp θ (x a).fst j γ := by
    intro a
    haveI := (hci a).1
    exact hC 𝓀[k] θ hθ (x a).fst (hcusp a).1 _ (levelZero (x a).rep) (hci a).2.1 (hci a).2.2
  choose c hreg htr using hch
  refine ⟨s, x, c, hmap, fun a => ⟨hcusp a, hdzx a, hreg a, htr a⟩, ?_⟩
  haveI : ∀ a, FiniteDimensional ℂ (fixed (x a).rep (KOne k (Fin (x a).fst))) := fun a => (hci a).1
  haveI hfinV : FiniteDimensional ℂ (fixed π (KOne k (Fin N))) := by
    obtain ⟨-, hadm⟩ := UpperTheory.Zero.LLC.Pr.adm k N V π hS.isSmooth hS.isIrreducible
    have := hadm (levelPre ⊥) (isOpen_levelPre ⊥) (isCompact_levelPre ⊥)
    rwa [levelPre_bot] at this
  obtain ⟨Φ, hΦ1, hΦ2⟩ := hTF k s (fun a => (x a).fst) (fun a => (x a).snd.rep.V) (fun a => (x a).rep)
    (fun a => (x a).snd.rep.smooth)
  obtain ⟨ψ, hψ0, hψ⟩ := hSQ k N s (fun a => (x a).fst) hd _ V _ (piTensor fun a => (x a).rep) π
    (piTensor fun a => levelZero (x a).rep) Φ hΦ1 hΦ2 hsub hfix
  obtain ⟨hfinZ, htrZ⟩ := hT s (fun a => GL (Fin (x a).fst) 𝓀[k])
    (fun a => fixed (x a).rep (KOne k (Fin (x a).fst))) (fun a => levelZero (x a).rep)
  obtain ⟨c0, hc0, hfr⟩ := hF 𝓀[k] s (fun a => (x a).fst) N hd
  have hmeet := ((hM (parab 𝓀[k] (stdBlocks (fun a => (x a).fst) hd)) _ _
    ((levelZero π).comp (parab 𝓀[k] (stdBlocks (fun a => (x a).fst) hd)).subtype)
    ((piTensor fun a => levelZero (x a).rep).comp
      (leviProj 𝓀[k] (stdBlocks (fun a => (x a).fst) hd)))).1).2 ⟨ψ, hψ0, fun p v => hψ p v⟩
  have hJD : JD θ [] (List.ofFn fun a => ((x a).fst, c a)) N =
      hcL (List.ofFn fun i => (⟨(x i).fst, cusp θ (x i).fst (c i)⟩ :
        (m : ℕ) × (GL (Fin m) 𝓀[k] → ℂ))) N := by
    rw [(hJ 𝓀[k] θ).1]
    simp [List.map_ofFn, Function.comp_def]
  refine ⟨⟨Finite.one_lt_card, by simp, ?_⟩, rfl, ?_, ?_⟩
  · intro p hp
    rw [List.mem_ofFn] at hp
    obtain ⟨a, rfl⟩ := hp
    exact ⟨(hcusp a).1, hreg a⟩
  · simp [Lbl.rk, GlobalTheory.Shin.deg, List.sum_ofFn, hd]
  · unfold Meets at hmeet ⊢
    rw [hJD, hfr _ _ (isCl_trace _)]
    refine mul_ne_zero hc0 ?_
    convert hmeet using 1
    refine finsum_congr fun p => ?_
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, htrZ, htr]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PLeRank
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem gcd_step {m m' c l : ℕ} (hm : 0 < m) (hl : l.Prime) (h : m' * Nat.gcd m c = m) :
    (if l ∣ m' then m' / l else m') * Nat.gcd m (c * l) = m := by
  have hg : 0 < Nat.gcd m c := Nat.gcd_pos_of_pos_left _ hm
  obtain ⟨m₁, c₁, hco, hm₁, hc₁⟩ := Nat.exists_coprime m c
  have hmm : m₁ = m' := by
    apply Nat.eq_of_mul_eq_mul_right hg
    rw [← hm₁, h]
  subst hmm
  set g := Nat.gcd m c with hgdef
  have hgcd : Nat.gcd m (c * l) = Nat.gcd m₁ l * g := by
    have e : c * l = (c₁ * l) * g := by
      rw [hc₁]; ring
    rw [e]
    conv_lhs => rw [hm₁]
    rw [Nat.gcd_mul_right, Nat.Coprime.gcd_mul_left_cancel_right l hco.symm]
  rw [hgcd]
  split_ifs with hd
  · rw [Nat.gcd_eq_right hd, ← mul_assoc, Nat.div_mul_cancel hd]
    exact h
  · have : Nat.gcd m₁ l = 1 := ((Nat.Prime.coprime_iff_not_dvd hl).2 hd).symm
    rw [this, one_mul]
    exact h

theorem UpperTheory.Gal.InertialTypesAlt.leRank :
    LiftOk → LeRank := by
  intro hOk a b ha hab
  have key : b.Ok ∧ ∃ c : ℕ, 0 < c ∧ b.q = a.q ^ c ∧
      ∀ p ∈ b.L, ∃ r ∈ a.L, p.1 * Nat.gcd r.1 c = r.1 := by
    induction hab with
    | refl =>
      refine ⟨ha, 1, Nat.one_pos, (pow_one _).symm, fun p hp => ⟨p, hp, ?_⟩⟩
      rw [Nat.gcd_one_right, mul_one]
    | @tail b' b'' _ hs ih =>
      obtain ⟨hb, c, hc, hq, hL⟩ := ih
      obtain ⟨l, hl, rfl⟩ := hs
      refine ⟨(hOk b' l hl hb).1, c * l, Nat.mul_pos hc hl.pos, ?_, ?_⟩
      · change b'.q ^ l = _
        rw [hq, pow_mul]
      · intro p hp
        have hp' : p ∈ liftAll b'.q l b'.L := hp
        unfold liftAll at hp'
        obtain ⟨s, hs, hps⟩ := List.mem_flatMap.1 hp'
        obtain ⟨r, hr, hsr⟩ := hL s hs
        refine ⟨r, hr, ?_⟩
        have hm : 0 < r.1 := (ha.2.2 r hr).1
        have hstep := gcd_step (l := l) hm hl hsr
        have hp1 : p.1 = if l ∣ s.1 then s.1 / l else s.1 := by
          split_ifs at hps ⊢ with hd
          · simp only [liftL, List.flatMap_cons, List.flatMap_nil, List.append_nil, List.mem_map] at hps
            obtain ⟨i, -, rfl⟩ := hps
            rfl
          · simp only [List.mem_singleton] at hps
            rw [hps]
        rw [hp1]
        exact hstep
  exact key.2
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PPlaceEx
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

theorem UpperTheory.Gal.InertialTypesAlt.placeEx :
    PlaceEx := by
  intro K M Ω _ _ _ _ _ _ _ _ A v hv n P
  let f : 𝓞 M →+* A := ((algebraMap M Ω).comp (algebraMap (𝓞 M) M)).codRestrict A fun x =>
    ReciprocityTheory.Gal.mem_of_isIntegral_int A (map_isIntegral_int (algebraMap M Ω) x.isIntegral_coe)
  let I : Ideal (𝓞 M) := (IsLocalRing.maximalIdeal A).comap f
  have hmem : ∀ x : 𝓞 M, x ∈ I ↔ A.valuation (algebraMap M Ω (x : M)) < 1 := fun x =>
    ValuationSubring.valuation_lt_one_iff A (f x)
  have hN0 : Ideal.absNorm v.asIdeal ≠ 0 := Ideal.absNorm_eq_zero_iff.not.mpr v.ne_bot
  have hval : A.valuation ((Ideal.absNorm v.asIdeal : ℕ) : Ω) < 1 := by
    have h := (hv ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K)).2 (Ideal.absNorm_mem v.asIdeal)
    simpa using h
  have hne : I ≠ ⊥ := by
    intro h0
    have h1 : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 M) ∈ I := (hmem _).2 (by simpa using hval)
    rw [h0, Ideal.mem_bot] at h1
    exact Nat.cast_ne_zero.2 hN0 h1
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp GlobalTheory.automorphicFormsFiniteGL M n P
    ⟨I, Ideal.comap_isPrime _ _, hne⟩
  exact ⟨⟨I, Ideal.comap_isPrime _ _, hne⟩, fun x => (hmem x).symm, τ, hτ⟩
end

