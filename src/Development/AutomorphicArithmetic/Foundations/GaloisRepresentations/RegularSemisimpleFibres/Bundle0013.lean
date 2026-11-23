module

public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.Bundle0010
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.ResEmbCompat
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0016
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.CharacterTheory.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.Bundle0001
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0498
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.Multi
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0623

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PJdPair
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private lemma deg_app (a b : List (ℕ × ℕ)) : deg (a ++ b) = deg a + deg b := by
  simp [GlobalTheory.Shin.deg]

private lemma deg_rep (t c : ℕ) : deg (List.replicate t ((1 : ℕ), c)) = t := by
  simp [GlobalTheory.Shin.deg]

private lemma expand_cons' (p : ℕ × ℕ) (D : List (ℕ × ℕ)) :
    expand (p :: D) = List.replicate p.1 (1, p.2) ++ expand D := by
  simp [UpperTheory.Gal.InertialTypesAlt.expand]

private lemma cusp_one_ne {F : Type} [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ) (m k : ℕ)
    (hm : 0 < m) : cusp θ m k 1 ≠ 0 := by
  have h := GlobalTheory.T.invariantSubspaceMobiusInverse_one_prod_Ico F (Fin m → F) (GlobalTheory.CuspGL.rootSum θ k) (_root_.GlobalTheory.CuspGL.rootSum_isAdditive_and_pow_X_sub_one F θ k).2 (by simpa using hm)
  simp only [cusp, psiG, Units.val_one, Matrix.toLin'_one]
  erw [h]
  apply mul_ne_zero (pow_ne_zero _ (by norm_num))
  rw [Finset.prod_ne_zero_iff]
  intro i hi
  have hq : 1 < Nat.card F := Finite.one_lt_card
  have hi1 : 1 ≤ i := (Finset.mem_Ico.mp hi).1
  rw [sub_ne_zero]
  intro heq
  have h2 : ((Nat.card F ^ i : ℕ) : ℂ) = 1 := by
    push_cast
    exact heq.symm
  norm_cast at h2
  have h3 := Nat.one_lt_pow (by omega : i ≠ 0) hq
  omega

private lemma pairs_self {G : Type} [Group G] [Finite G] (Y : G → ℂ) (h : Y 1 ≠ 0) : Pairs Y Y := by
  haveI : Fintype G := Fintype.ofFinite G
  unfold Pairs
  rw [finsum_eq_sum_of_fintype]
  intro h0
  have hre := congrArg Complex.re h0
  rw [Complex.re_sum, Complex.zero_re] at hre
  have hnn : ∀ g : G, 0 ≤ (star (Y g) * Y g).re := by
    intro g
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    exact Complex.normSq_nonneg _
  have hpos : 0 < (star (Y 1) * Y 1).re := by
    rw [Complex.star_def, ← Complex.normSq_eq_conj_mul_self, Complex.ofReal_re]
    exact Complex.normSq_pos.mpr h
  have : 0 < ∑ g : G, (star (Y g) * Y g).re :=
    Finset.sum_pos' (fun g _ => hnn g) ⟨1, Finset.mem_univ _, hpos⟩
  linarith

private lemma happ (hA : JAppend) {F : Type} [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (R M : List (ℕ × ℕ)) (t b n : ℕ) (hR : deg R = t) (hM : deg M = b) (hn : n = t + b) :
    J θ (R ++ M) n = hc t b (J θ R t) (J θ M b) n := by
  subst hR hM hn
  exact hA F θ R M _ rfl

private lemma char_cast {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (M : List (ℕ × ℕ)) {n m : ℕ}
    (e : n = m) (h : GlobalTheory.BI.IsChar ℂ ℂ (J θ M n)) : GlobalTheory.BI.IsChar ℂ ℂ (J θ M m) := by
  subst e
  exact h

private lemma J_one_ne (h1 : HcOne) {F : Type} [Field F] [Finite F] (θ : AlgebraicClosure F →* ℂ)
    (M : List (ℕ × ℕ)) (hM : ∀ p ∈ M, 0 < p.1) : J θ M (deg M) 1 ≠ 0 := by
  induction M with
  | nil =>
    rw [J_nil]
    exact one_ne_zero
  | cons p M ih =>
    have hp : 0 < p.1 := hM p (by simp)
    have hM' : ∀ x ∈ M, 0 < x.1 := fun x hx => hM x (by simp [hx])
    rw [J_cons]
    exact h1 F p.1 (deg M) _ (by simp [GlobalTheory.Shin.deg]) _ _ (cusp_one_ne θ p.1 p.2 hp) (ih hM')

theorem UpperTheory.Gal.InertialTypesAlt.jdPair :
    JAppend → HcOne → HcPair → DetPair → JDChar → JDPair := by
  intro hA h1 hP hD hC F _ _ θ hθ a ha hq
  obtain ⟨q, D, L⟩ := a
  obtain ⟨hq2, hDp, hLp⟩ := ha
  have hL0 : ∀ x ∈ L, 0 < x.1 := fun x hx => (hLp x hx).1
  have charJ : ∀ M : List (ℕ × ℕ), (∀ x ∈ M, 0 < x.1 ∧ Reg q x.1 x.2) → ∀ n, n = deg M →
      GlobalTheory.BI.IsChar ℂ ℂ (J θ M n) := by
    intro M hM n hn
    have hc := (hC F θ hθ).2 ⟨q, [], M⟩ ⟨hq2, by simp, hM⟩ hq
    simp only [Lbl.D, Lbl.L, Lbl.rk] at hc
    rw [JD_nil] at hc
    exact char_cast θ M (by simp [GlobalTheory.Shin.deg] at hn ⊢; omega) hc
  have key : ∀ E : List (ℕ × ℕ), (∀ x ∈ E, 0 < x.1) →
      deg (expand E ++ L) = deg E + deg L ∧
        Pairs (J θ (expand E ++ L) (deg E + deg L)) (JD θ E L (deg E + deg L)) := by
    intro E
    induction E with
    | nil =>
      intro _
      have e1 : expand [] ++ L = L := by simp [UpperTheory.Gal.InertialTypesAlt.expand]
      have e2 : deg ([] : List (ℕ × ℕ)) = 0 := by simp [GlobalTheory.Shin.deg]
      rw [e1, e2, zero_add, JD_nil]
      exact ⟨rfl, pairs_self _ (J_one_ne h1 θ L hL0)⟩
    | cons p E ih =>
      intro hp
      have hp1 : 0 < p.1 := hp p (by simp)
      have hE : ∀ x ∈ E, 0 < x.1 := fun x hx => hp x (by simp [hx])
      obtain ⟨hdeg, hpair⟩ := ih hE
      have hdc : deg (p :: E) = p.1 + deg E := by simp [GlobalTheory.Shin.deg]
      have hexp : ∀ x ∈ expand E ++ L, 0 < x.1 ∧ Reg q x.1 x.2 := by
        intro x hx
        rcases List.mem_append.mp hx with h | h
        · simp only [UpperTheory.Gal.InertialTypesAlt.expand, List.mem_flatMap, List.mem_replicate] at h
          obtain ⟨y, -, -, rfl⟩ := h
          exact ⟨Nat.one_pos, fun i hi hi1 => absurd hi1 (by omega)⟩
        · exact hLp x h
      have hrep : ∀ x ∈ List.replicate p.1 ((1 : ℕ), p.2), 0 < x.1 ∧ Reg q x.1 x.2 := by
        intro x hx
        rw [List.mem_replicate] at hx
        rw [hx.2]
        exact ⟨Nat.one_pos, fun i hi hi1 => absurd hi1 (by omega)⟩
      rw [expand_cons', List.append_assoc, deg_app, deg_rep, hdeg, hdc]
      refine ⟨by omega, ?_⟩
      rw [happ hA θ _ _ p.1 (deg E + deg L) _ (deg_rep _ _) hdeg (by omega), JD_cons]
      refine hP F p.1 _ _ (by omega) _ _ _ _ ((hC F θ hθ).1 _ _)
        (charJ _ hrep _ (deg_rep _ _).symm) ((hC F θ hθ).2 ⟨q, E, L⟩ ⟨hq2, hE, hLp⟩ hq)
        (charJ _ hexp _ hdeg.symm) (hD F θ p.1 p.2) hpair
  exact key D hDp
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PKillsTrue
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem JD_cons' {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (p : ℕ × ℕ) (D L : List (ℕ × ℕ))
    (b n : ℕ) (h : deg D + deg L = b) :
    JD θ (p :: D) L n = hc p.1 b (detc θ p.1 p.2) (JD θ D L b) n := by
  subst h; rfl

private theorem isCl_detc {F : Type} [Field F] (θ : AlgebraicClosure F →* ℂ) (t k : ℕ) : IsCl (detc θ t k) := by
  intro x y
  have hd : ((y⁻¹ * x * y : GL (Fin t) F) : Matrix (Fin t) (Fin t) F).det =
      (x : Matrix (Fin t) (Fin t) F).det := by
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul,
      mul_comm (Matrix.det ((y⁻¹ : GL (Fin t) F) : Matrix (Fin t) (Fin t) F)), mul_assoc,
      ← Matrix.det_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.det_one, mul_one]
  simp only [detc, hd]

private theorem gen_of_frob {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F'] (s : F' ≃ₐ[F] F')
    (hs : ∀ z, s z = z ^ Nat.card F) (t : F' ≃ₐ[F] F') : t ∈ Subgroup.zpowers s := by
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  have : Fintype F := Fintype.ofFinite F
  have hs' : s = FiniteField.frobeniusAlgEquivOfAlgebraic F F' := by
    ext z
    simp [hs z, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, Nat.card_eq_fintype_card]
  obtain ⟨n, hn⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow F F').2 t
  rw [hs']
  exact ⟨(n.1 : ℤ), by simpa using hn⟩

private theorem card_lift {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F'] :
    Nat.card F ^ Module.finrank F F' = Nat.card F' := by
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  exact Module.natCard_eq_pow_finrank.symm

private theorem step (hLH : LiftHc) (hKH : KillsHc) (hNE : NormEx) (hJE : JDEq) (hJC : JDChar) (hLD : LiftDet)
    {F F' : Type} [Field F] [Field F'] [Algebra F F'] [Finite F'] [Finite F] (s : F' ≃ₐ[F] F')
    (hs : ∀ z, s z = z ^ Nat.card F) (ι : AlgebraicClosure F →ₐ[F] AlgebraicClosure F')
    (θ : AlgebraicClosure F' →* ℂ) (hθ : Inj θ) (p : ℕ × ℕ) (D L D' L' : List (ℕ × ℕ)) (b n : ℕ)
    (hn : n = p.1 + b) (h₁ : deg D + deg L = b) (h₂ : deg D' + deg L' = b)
    (hB : GlobalTheory.BI.IsChar ℂ ℂ (JD θ D' L' b))
    (IH : Kills (shLift s (JD (pullθ ι θ) D L b)) (JD θ D' L' b)) :
    Kills (shLift s (JD (pullθ ι θ) (p :: D) L n))
      (JD θ ((p.1, p.2 * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ i) :: D') L' n) := by
  have hg : ∀ t : F' ≃ₐ[F] F', t ∈ Subgroup.zpowers s := gen_of_frob s hs
  rw [JD_cons' (pullθ ι θ) p D L b n h₁, JD_cons' θ _ D' L' b n h₂]
  rw [hLH F F' s hg p.1 b n hn _ _ (isCl_detc _ _ _) ((hJE F (pullθ ι θ)).2.2 D L b)]
  rw [hLD F F' s hs ι θ p.1 p.2 (hNE F F' s hs p.1)]
  exact hKH F' (s : F' →+* F') p.1 b n hn _ _ _ _ ((hJC F' θ hθ).1 _ _) hB
    (kills_self _ _ ((hJC F' θ hθ).1 _ _)) IH

theorem UpperTheory.Gal.InertialTypesAlt.killsTrue :
    (KillsOn fun a => a.D = []) → LiftHc → KillsHc → NormEx → LiftOk → JDEq → JDChar → LiftDet → KillsOn fun _ => True := by
  intro h0 hLH hKH hNE hLO hJE hJC hLD F F' _ _ _ _ s hl hs ι θ hθ a _ hok hq
  have : Finite F := Finite.of_injective _ (algebraMap F F').injective
  have hlift := hLO a (Module.finrank F F') hl hok
  obtain ⟨q, D0, L0⟩ := a
  change q = Nat.card F at hq
  subst hq
  have hok' := hok
  unfold Lbl.Ok at hok'
  obtain ⟨hq2, hDpos, hLok⟩ := hok'
  have hl1 := hlift.1
  unfold Lbl.Ok at hl1
  obtain ⟨hq2', _, hLok'⟩ := hl1
  have hdegmap : ∀ D : List (ℕ × ℕ),
      deg (D.map fun p => (p.1, p.2 * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ i)) =
        deg D := by
    intro D
    simp [GlobalTheory.Shin.deg, List.map_map, Function.comp_def]
  have hdegL : deg (liftAll (Nat.card F) (Module.finrank F F') L0) = deg L0 := by
    have h := hlift.2
    simp only [Lbl.rk, Lbl.lift, hdegmap] at h
    omega
  have key : ∀ D : List (ℕ × ℕ), (∀ p ∈ D, 0 < p.1) →
      Kills (shLift s (JD (pullθ ι θ) D L0 (deg D + deg L0)))
        (JD θ (D.map fun p => (p.1, p.2 * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ i))
          (liftAll (Nat.card F) (Module.finrank F F') L0) (deg D + deg L0)) := by
    intro D
    induction D with
    | nil =>
      intro _
      exact h0 F F' s hl hs ι θ hθ ⟨Nat.card F, [], L0⟩ rfl
        (by unfold Lbl.Ok; exact ⟨hq2, by simp, hLok⟩) rfl
    | cons p D ih =>
      intro hD
      have hD' : ∀ x ∈ D, 0 < x.1 := fun x hx => hD x (List.mem_cons_of_mem _ hx)
      have tr : ∀ (D' L' : List (ℕ × ℕ)) (n m : ℕ), n = m →
          GlobalTheory.BI.IsChar ℂ ℂ (JD θ D' L' n) → GlobalTheory.BI.IsChar ℂ ℂ (JD θ D' L' m) := by
        intro D' L' n m h
        subst h
        exact id
      have hB : GlobalTheory.BI.IsChar ℂ ℂ (JD θ
          (D.map fun p => (p.1, p.2 * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ i))
          (liftAll (Nat.card F) (Module.finrank F F') L0) (deg D + deg L0)) := by
        have hc := (hJC F' θ hθ).2 ⟨Nat.card F ^ Module.finrank F F',
          D.map fun p => (p.1, p.2 * ∑ i ∈ Finset.range (Module.finrank F F'), Nat.card F ^ i),
          liftAll (Nat.card F) (Module.finrank F F') L0⟩
          (by
            unfold Lbl.Ok
            refine ⟨hq2', ?_, hLok'⟩
            intro x hx
            obtain ⟨y, hy, rfl⟩ := List.mem_map.1 hx
            exact hD' y hy) card_lift
        refine tr _ _ _ _ ?_ hc
        show deg _ + deg _ = _
        rw [hdegmap, hdegL]
      exact step hLH hKH hNE hJE hJC hLD s hs ι θ hθ p D L0 _ _ (deg D + deg L0) _
        (by simp only [GlobalTheory.Shin.deg, List.map_cons, List.sum_cons]; omega) rfl
        (by rw [hdegmap, hdegL]) hB (ih hD')
  exact key D0 hDpos
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PLblFull
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem fd_fixed {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {N : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL (Fin N) k) V)
    (hs : IsSmooth π) (hi : π.IsIrreducible) : FiniteDimensional ℂ (fixed π (KOne k (Fin N))) := by
  refine (UpperTheory.Zero.LLC.Pr.adm k N V π hs hi).2 (KOne k (Fin N)) ?_ ?_
  · rw [← levelPre_bot]
    exact isOpen_levelPre _
  · rw [← levelPre_bot]
    exact isCompact_levelPre _

private theorem isCl_trace {G : Type} [Group G] {r : ℕ} (η : Representation ℂ G (Fin r → ℂ)) :
    IsCl (fun g => LinearMap.trace ℂ (Fin r → ℂ) (η g)) := by
  intro x y
  show LinearMap.trace ℂ _ (η (y⁻¹ * x * y)) = LinearMap.trace ℂ _ (η x)
  rw [map_mul, LinearMap.trace_mul_comm, ← map_mul, ← mul_assoc, mul_inv_cancel, one_mul]

private theorem frob_step (hF : FrobL) {F : Type} [Field F] [Finite F] {s : ℕ} {d : Fin s → ℕ} {N : ℕ}
    (hd : ∑ i, d i = N) (Y : ∀ i, GL (Fin (d i)) F → ℂ) {r : ℕ}
    (η : Representation ℂ (GL (Fin N) F) (Fin r → ℂ))
    (h : ∑ᶠ g, star (hcL (List.ofFn fun i => ⟨d i, Y i⟩) N g) * LinearMap.trace ℂ (Fin r → ℂ) (η g) ≠ 0) :
    ∑ᶠ p : parab F (stdBlocks d hd), star (∏ i, Y i (leviProj F (stdBlocks d hd) p i)) *
      LinearMap.trace ℂ (Fin r → ℂ) (η p) ≠ 0 := by
  obtain ⟨c, hc, hcY⟩ := hF F s d N hd
  intro h0
  apply h
  rw [hcY Y (fun g => LinearMap.trace ℂ (Fin r → ℂ) (η g)) (isCl_trace η), h0, mul_zero]

private theorem meets_parab (hT : TensTr) {F : Type} [Field F] {s : ℕ} {d : Fin s → ℕ} {N : ℕ}
    (hd : ∑ i, d i = N) {W : Fin s → Type} [∀ a, AddCommGroup (W a)] [∀ a, Module ℂ (W a)]
    [∀ a, FiniteDimensional ℂ (W a)] (σ : ∀ a, Representation ℂ (GL (Fin (d a)) F) (W a))
    (Y : ∀ i, GL (Fin (d i)) F → ℂ) (hY : ∀ a γ, LinearMap.trace ℂ (W a) (σ a γ) = Y a γ) {r : ℕ}
    (η : Representation ℂ (GL (Fin N) F) (Fin r → ℂ))
    (h : ∑ᶠ p : parab F (stdBlocks d hd), star (∏ i, Y i (leviProj F (stdBlocks d hd) p i)) *
      LinearMap.trace ℂ (Fin r → ℂ) (η p) ≠ 0) :
    Meets (η.comp (parab F (stdBlocks d hd)).subtype)
      (fun p => LinearMap.trace ℂ _ (((piTensor σ).comp (leviProj F (stdBlocks d hd))) p)) := by
  have key : ∀ p : parab F (stdBlocks d hd),
      LinearMap.trace ℂ (PiTensorProduct ℂ fun a => W a) (piTensor σ (leviProj F (stdBlocks d hd) p)) =
        ∏ i, Y i (leviProj F (stdBlocks d hd) p i) := by
    intro p
    rw [(hT s _ W σ).2]
    exact Finset.prod_congr rfl fun a _ => hY a _
  unfold Meets
  simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, key]
  exact h

private theorem compose_map {G X U U' : Type} [Group G] [AddCommGroup X] [Module ℂ X] [AddCommGroup U] [Module ℂ U]
    [AddCommGroup U'] [Module ℂ U'] {ρ : Representation ℂ G U} {ρ' : Representation ℂ G U'}
    {η : Representation ℂ G X} (Ψ : X →ₗ[ℂ] U) (f : ρ.IntertwiningMap ρ') (hf : Function.Injective f)
    (hΨ0 : Ψ ≠ 0) (hΨ : ∀ g x, Ψ (η g x) = ρ g (Ψ x)) :
    ∃ F : X →ₗ[ℂ] U', F ≠ 0 ∧ ∀ g x, F (η g x) = ρ' g (F x) := by
  refine ⟨f.toLinearMap ∘ₗ Ψ, ?_, ?_⟩
  · intro h0
    apply hΨ0
    refine LinearMap.ext fun x => hf ?_
    have := LinearMap.congr_fun h0 x
    simpa using this
  · intro g x
    have := LinearMap.congr_fun (f.isIntertwining' g) (Ψ x)
    simpa [hΨ] using this

theorem UpperTheory.Gal.InertialTypesAlt.lblFull :
    MeetsIff → FrobL → JDEq → TensTr → AvgMap → IndMap → TensInc → UpperTheory.Gal.InertialTypesAlt.LblFull := by
  intro hMI hF hJD hTT hAvg hInd hTI
  intro k _ _ _ _ _ θ N V _ _ π hs hi s x c hd hE hx T hT hP
  obtain ⟨e⟩ := hE
  obtain ⟨r, η, hη⟩ := hT
  have hTη : T = fun g => LinearMap.trace ℂ (Fin r → ℂ) (η g) := by
    funext g
    rw [hη g]
    rfl
  subst hTη
  have hJ : J θ (List.ofFn fun a => ((x a).fst, c a)) N =
      hcL (List.ofFn fun i => (⟨(x i).fst, cusp θ (x i).fst (c i)⟩ : (m : ℕ) × (GL (Fin m) 𝓀[k] → ℂ))) N := by
    rw [← JD_nil, (hJD 𝓀[k] θ).1]
    simp [List.map_ofFn, Function.comp_def]
  have h1 : ∑ᶠ g, star (hcL (List.ofFn fun i => (⟨(x i).fst, cusp θ (x i).fst (c i)⟩ :
      (m : ℕ) × (GL (Fin m) 𝓀[k] → ℂ))) N g) * LinearMap.trace ℂ (Fin r → ℂ) (η g) ≠ 0 := by
    rw [← hJ]
    exact hP
  have h2 := frob_step hF (d := fun a => (x a).fst) hd (fun i => cusp θ (x i).fst (c i)) η h1
  haveI hfd : ∀ a, FiniteDimensional ℂ (fixed (x a).rep (KOne k (Fin (x a).fst))) :=
    fun a => fd_fixed _ (x a).snd.rep.smooth (x a).snd.rep.irr
  have h3 := meets_parab hTT hd (fun a => levelZero (x a).rep) (fun i => cusp θ (x i).fst (c i)) hx η h2
  haveI := (hTT s _ _ (fun a => levelZero (x a).rep)).1
  obtain ⟨ψ, hψ0, hψ⟩ := ((hMI _ _ _ _ _).1).1 h3
  obtain ⟨j, hj, hjx⟩ := hTI k s (fun a => (x a).fst) _ (fun a => (x a).rep)
  obtain ⟨Φ, ev, hΦ1, hΦ2, hΦ3⟩ := hInd k N s (fun a => (x a).fst) hd _ _ _ _ j hj hjx
  obtain ⟨Ψ, hΨ0, hΨ⟩ := hAvg _ (parab 𝓀[k] (stdBlocks (fun a => (x a).fst) hd)) _ _ _ _ _ _ η Φ ev ψ
    hΦ1 hΦ2 hΦ3 hψ hψ0
  have hinj : Function.Injective (levelZeroMap e.symm.toIntertwiningMap) := by
    apply levelZeroMap_injective
    intro a b hab
    have := congrArg e hab
    simpa using this
  obtain ⟨F', hF0, hF'⟩ := compose_map Ψ (levelZeroMap e.symm.toIntertwiningMap) hinj hΨ0 hΨ
  haveI := fd_fixed π hs hi
  exact ((hMI _ _ _ (levelZero π) η).2).2 ⟨F', hF0, hF'⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PMixType
section
open NumberField IsDedekindDomain ValuativeRel Polynomial Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.L2.Host
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.Shin
open GroundTheory.Global GroundTheory.Global.SemiLocal UpperTheory.V.Published UpperTheory.CBC UpperTheory.Gal.InertialTypesAlt
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

private theorem inj_comp {F R : Type} [Field F] [Field R] (Θ : R →* ℂ) (hΘ : Inj Θ) (e : F →+* R) :
    Inj (Θ.comp e.toMonoidHom) := by
  intro x y hx hy hxy
  have hx' : e x ≠ 0 := by simpa using hx
  have hy' : e y ≠ 0 := by simpa using hy
  exact e.injective (hΘ _ _ hx' hy' hxy)

private theorem cast_eq_of_pow {k : Type} [Field k] [Finite k] (θ : AlgebraicClosure k →* ℂ) (hθ : Inj θ)
    (c c' : ℕ) (h : ∀ u : kˣ, θ (algebraMap k _ (u : k)) ^ c = θ (algebraMap k _ (u : k)) ^ c') :
    ((c : ℕ) : ZMod (Nat.card k - 1)) = ((c' : ℕ) : ZMod (Nat.card k - 1)) := by
  obtain ⟨ζ, hζ⟩ := IsCyclic.exists_generator (α := kˣ)
  have hord : orderOf ζ = Nat.card k - 1 := by
    rw [orderOf_eq_card_of_forall_mem_zpowers hζ, Nat.card_units]
  have hz : algebraMap k (AlgebraicClosure k) (ζ : k) ≠ 0 := by simp
  have h1 : θ (algebraMap k (AlgebraicClosure k) (ζ : k) ^ c) = θ (algebraMap k (AlgebraicClosure k) (ζ : k) ^ c') := by
    rw [map_pow θ, map_pow θ]; exact h ζ
  have h2 := hθ _ _ (pow_ne_zero _ hz) (pow_ne_zero _ hz) h1
  have h3 : ζ ^ c = ζ ^ c' := by
    apply Units.ext
    apply (algebraMap k (AlgebraicClosure k)).injective
    simpa using h2
  rw [pow_eq_pow_iff_modEq, hord] at h3
  exact (ZMod.natCast_eq_natCast_iff _ _ _).2 h3

theorem UpperTheory.Gal.InertialTypesAlt.mixType :
    (LblOn fun _ => True) → LblMixed → SepOf → LeTop → PolTop → TypeOfLbl → ResEmbEx → BaseQ → CardRes → MixType := by
  intro hOn hMix hSep hTop hPol hType hEmb hBase hCard E Ω _ _ _ _ _ _ n hn π Y hY A v w h h' g _ i hi hI τ τ' hτ hτ' hM f hf hs
  obtain ⟨⟨e, he⟩, Θ, hΘ⟩ := hEmb E Ω A v h
  obtain ⟨⟨e', he'⟩, -⟩ := hEmb Y.K Ω A w h'
  obtain ⟨a, s, ha, hApart, hS, hL⟩ := hMix E Ω A v h g i hi (Θ.comp e.toMonoidHom) (inj_comp Θ hΘ e) n τ hM
  obtain ⟨b, hab, hb⟩ := hOn E Ω n hn (Pt.base Ω π) Y hY A Θ hΘ hI v w h h' e e' he he' τ τ' hτ hτ' a trivial ha
  have hag : a.q = g := ha.2.1.trans (hBase E v g i hi).2.1
  have hbQ : b.q = g ^ f := by rw [hb.2.1, hCard, hf]
  have hb2 : 2 ≤ b.q := hb.1.1
  have hf0 : 0 < f := by
    rcases Nat.eq_zero_or_pos f with h0 | h0
    · rw [hbQ, h0] at hb2; simp at hb2
    · exact h0
  have hsp : a.Splits b.q := ⟨f, hf0, by rw [hbQ, hag], fun p hp => by
    obtain ⟨y, hy, hyp⟩ := hL p hp
    rw [← hyp]; exact hs s hS y hy⟩
  obtain ⟨-, -, hL1, hbl⟩ := hTop a b ha.1 hab hsp
  have hsep : b.Sep b.q := by
    have := hSep a b.q ha.1 hApart hsp
    unfold Lbl.Sep at this ⊢
    rwa [hbl]
  obtain ⟨c, d, k, hd, ω, hlist, hω, hT⟩ := hType _ (Θ.comp e'.toMonoidHom) n _ τ'.ρ b hb hL1
  have hbl2 := (hPol b 1 hb2 hL1 (one_pow _)).1
  have hinj : Function.Injective fun x : Fin c => ((k x : ℕ) : ZMod (b.q - 1)) := by
    unfold Lbl.Sep at hsep
    rw [hbl2, hlist.symm] at hsep
    rw [Multiset.map_coe, Multiset.coe_nodup] at hsep
    simp only [List.map_ofFn] at hsep
    exact List.nodup_ofFn.1 hsep
  have : Finite 𝓀[w.adicCompletion Y.K] := Nat.finite_of_card_ne_zero (by rw [← hb.2.1]; omega)
  refine ⟨c, d, hd, ω, ?_, ?_, hT⟩
  · intro x
    have hmem : (d x, k x) ∈ b.D ++ b.L := by
      rw [← hlist]; exact (List.mem_ofFn' _ _).2 ⟨x, rfl⟩
    rcases List.mem_append.1 hmem with hm | hm
    · exact hb.1.2.1 _ hm
    · exact (hb.1.2.2 _ hm).1
  · intro x x' hxx
    apply hinj
    have := cast_eq_of_pow (Θ.comp e'.toMonoidHom) (inj_comp Θ hΘ e') (k x) (k x') (fun u => by
      rw [← hω x u, ← hω x' u, hxx])
    rw [← hb.2.1] at this
    exact this
end

