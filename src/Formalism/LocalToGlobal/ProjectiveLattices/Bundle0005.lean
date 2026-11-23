module

public import Formalism.LocalToGlobal.ProjectiveLattices.AlgebraMapCAt
public import Formalism.LocalToGlobal.ProjectiveLattices.OneLtAbsNormReal

@[expose] public section

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ChartWD
section
noncomputable section

namespace Formalism.L2.Pj

section Charts

variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)

abbrev locM (K : Type) [Field K] {S : Type} [CommRing S] [Algebra K S] (m : Ideal S) [m.IsPrime] :
    S →ₐ[K] Localization.AtPrime m :=
  IsScalarTower.toAlgHom K S (Localization.AtPrime m)

def FrChartAt {S : Type} [CommRing S] [Algebra K S] (w : pts S) (m : Ideal S) [m.IsPrime] (A : TRing K)
    (u : pts A.R) (c : A.R →ₐ[K] Localization.AtPrime m) : Prop :=
  ∀ (p : TRing K) (φ : p.R →ₐ[K] S) (y : pts p.R), mapR φ y w →
    ∃ (p' : TRing K) (lam : p.R →ₐ[K] p'.R) (a : A.R →ₐ[K] p'.R) (μ : p'.R →ₐ[K] Localization.AtPrime m)
      (y' : pts p'.R), mapR lam y y' ∧ mapR a u y' ∧ μ.comp lam = (locM K m).comp φ ∧ μ.comp a = c

def FrChart : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra K S] (w : pts S) (m : Ideal S) [m.IsMaximal],
    ∃ (A : TRing K) (u : pts A.R) (c : A.R →ₐ[K] Localization.AtPrime m), FrChartAt pts mapR w m A u c

def BorChart : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ) (w w' : pts S), borR t w w' →
    ∀ (m : Ideal S) [m.IsMaximal],
      ∃ (A : TRing K) (u : pts A.R) (c c' : A.R →ₐ[K] Localization.AtPrime m) (B : TRing K) (uB uB' : pts B.R)
        (tB : ι → (B.R)ˣ) (π π' : A.R →ₐ[K] B.R) (cB : B.R →ₐ[K] Localization.AtPrime m),
        FrChartAt pts mapR w m A u c ∧ FrChartAt pts mapR w' m A u c' ∧ mapR π u uB ∧ mapR π' u uB' ∧
          borR tB uB uB' ∧ cB.comp π = c ∧ cB.comp π' = c' ∧ ∀ i, cB (tB i : B.R) = locM K m (t i : S)

variable {pts mapR borR}

theorem chartAt_val {f : Rules pts} (hf : IsNatural pts mapR f) {S : Type} [CommRing S] [Algebra K S] {w : pts S}
    {m : Ideal S} [m.IsPrime] {A : TRing K} {u : pts A.R} {c : A.R →ₐ[K] Localization.AtPrime m}
    (hc : FrChartAt pts mapR w m A u c) {p : TRing K} {φ : p.R →ₐ[K] S} {y : pts p.R} (hy : mapR φ y w) :
    locM K m (φ (f p y)) = c (f A u) := by
  obtain ⟨p', lam, a, μ, y', h1, h2, h3, h4⟩ := hc p φ y hy
  have e1 : f p' y' = lam (f p y) := hf p p' lam y y' h1
  have e2 : f p' y' = a (f A u) := hf A p' a u y' h2
  calc locM K m (φ (f p y)) = ((locM K m).comp φ) (f p y) := rfl
    _ = (μ.comp lam) (f p y) := by rw [h3]
    _ = μ (f p' y') := by rw [e1]; rfl
    _ = (μ.comp a) (f A u) := by rw [e2]; rfl
    _ = c (f A u) := by rw [h4]

theorem eq_of_locM {S : Type} [CommRing S] [Algebra K S] {x y : S}
    (h : ∀ (m : Ideal S) (_ : m.IsMaximal), locM K m x = locM K m y) : x = y := by
  rw [← sub_eq_zero]
  apply eq_zero_of_localization
  intro J hJ
  haveI := hJ
  have hxy := h J hJ
  simp only [locM, IsScalarTower.coe_toAlgHom'] at hxy
  rw [map_sub, hxy, sub_self]

theorem evalWD_of_frChart (h : FrChart pts mapR) : EvalWD pts mapR := by
  intro f hf S _ _ p q φ ψ y z w hy hz
  apply eq_of_locM (K := K)
  intro m hm
  haveI := hm
  obtain ⟨A, u, c, hc⟩ := h S w m
  rw [chartAt_val hf hc hy, chartAt_val hf hc hz]

private theorem evalAt_spec_lemma {f : Rules pts} {S : Type} [CommRing S] [Algebra K S] {y : pts S}
    (hy : FromTest pts mapR y) : ∃ (p : TRing K) (φ : p.R →ₐ[K] S) (y0 : pts p.R),
      mapR φ y0 y ∧ evalAt pts mapR f y = φ (f p y0) := by
  refine ⟨hy.choose, hy.choose_spec.choose, hy.choose_spec.choose_spec.choose,
    hy.choose_spec.choose_spec.choose_spec, ?_⟩
  rw [evalAt, dite_eq_left hy]

theorem wtAll_of_borChart [Fintype ι] (h : BorChart pts mapR borR) (e : ι → ℕ) {f : Rules pts}
    (hf : IsNatural pts mapR f) (hw : IsWeight pts borR e f) (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ)
    (y y' : pts S) (hy : FromTest pts mapR y) (hy' : FromTest pts mapR y') (hb : borR t y y') :
    evalAt pts mapR f y' = wchar e t * evalAt pts mapR f y := by
  obtain ⟨p, φ, y0, hm, hv⟩ := evalAt_spec_lemma (f := f) hy
  obtain ⟨p', φ', y0', hm', hv'⟩ := evalAt_spec_lemma (f := f) hy'
  rw [hv, hv']
  apply eq_of_locM (K := K)
  intro m hmax
  haveI := hmax
  obtain ⟨A, u, c, c', B, uB, uB', tB, π, π', cB, hc, hc', hπ, hπ', hbB, e1, e2, e3⟩ := h S t y y' hb m
  rw [map_mul, chartAt_val hf hc' hm', chartAt_val hf hc hm]
  calc c' (f A u) = (cB.comp π') (f A u) := by rw [e2]
    _ = cB (f B uB') := by rw [AlgHom.comp_apply, hf A B π' u uB' hπ']
    _ = cB (wchar e tB) * cB (f B uB) := by rw [hw B tB uB uB' hbB, map_mul]
    _ = locM K m (wchar e t) * c (f A u) := by
      have k1 : cB (f B uB) = c (f A u) := by rw [← e1, AlgHom.comp_apply, hf A B π u uB hπ]
      rw [k1]
      simp [wchar, map_prod, map_pow, e3, Units.coe_prod]

end Charts

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ComplSt
section
namespace Formalism.L2.Pj

def ComplSt : Prop :=
  ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [CharZero W],
    ∃ (T : CDVR) (ι : W →+* T.V), IsLocalHom ι ∧ ∃ ϖ : W, Irreducible ϖ ∧ Irreducible (ι ϖ)

end Formalism.L2.Pj
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.ReadAlg
section
noncomputable section

namespace Formalism.L2.Pj

open MvPolynomial

section Alg

variable {K : Type} [Field K]

theorem eq_zero_of_pts {M : Type} [Field M] [IsAlgClosed M] [Algebra K M] (p : TRing K) (a : p.R)
    (h : ∀ ψ : p.R →ₐ[K] M, ψ a = 0) : a = 0 := by
  classical
  have hRdef : p.R = (MvPolynomial (Fin p.n) K ⧸ p.I) := rfl
  haveI : IsReduced p.R := (Ideal.isRadical_iff_quotient_reduced p.I).1 p.rad
  haveI : IsJacobsonRing p.R := inferInstanceAs (IsJacobsonRing (MvPolynomial (Fin p.n) K ⧸ p.I))
  haveI hFT : Algebra.FiniteType K p.R :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K p.I) (Ideal.Quotient.mkₐ_surjective K p.I)
  have hrad : (⊥ : Ideal p.R).IsRadical := fun x ⟨k, hk⟩ =>
    (Submodule.mem_bot _).2 (IsNilpotent.eq_zero ⟨k, (Submodule.mem_bot _).1 hk⟩)
  have hjac : (⊥ : Ideal p.R).jacobson = ⊥ := by
    first
    | exact IsJacobsonRing.out inferInstance hrad
    | exact IsJacobsonRing.out' ⊥ hrad
  have ha : a ∈ (⊥ : Ideal p.R).jacobson := by
    set_option synthInstance.maxHeartbeats 400000 in
    refine Ideal.mem_sInf.2 fun J hJ => ?_
    have hJm : J.IsMaximal := hJ.2
    letI := Ideal.Quotient.field J
    haveI : Algebra.FiniteType K (p.R ⧸ J) :=
      Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ K J) (Ideal.Quotient.mkₐ_surjective K J)
    haveI : Module.Finite K (p.R ⧸ J) := finite_of_finite_type_of_isJacobsonRing K (p.R ⧸ J)
    haveI : Algebra.IsIntegral K (p.R ⧸ J) := Algebra.IsIntegral.of_finite K _
    haveI : Algebra.IsAlgebraic K (p.R ⧸ J) := Algebra.IsIntegral.isAlgebraic
    let ι : (p.R ⧸ J) →ₐ[K] M := (by
      refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
      solve_by_elim* (maxDepth := 2) only [*,
        @_root_.DivisionSemiring.to_moduleIsTorsionFree,
        @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
    have h0 := h (ι.comp (Ideal.Quotient.mkₐ K J))
    have h1 : ι (Ideal.Quotient.mk J a) = ι 0 := by
      rw [map_zero]
      exact h0
    exact Ideal.Quotient.eq_zero_iff_mem.1 (ι.toRingHom.injective h1)
  rw [hjac] at ha
  exact (Submodule.mem_bot _).1 ha

theorem eq_zero_of_cpts (σ : K →+* ℂ) (p : TRing K) (a : p.R) (h : ∀ ψ : p.R →ₐ[K] CAt σ, ψ a = 0) : a = 0 := by
  letI : Field (CAt σ) := inferInstanceAs (Field ℂ)
  haveI : IsAlgClosed (CAt σ) := inferInstanceAs (IsAlgClosed ℂ)
  exact eq_zero_of_pts (M := CAt σ) p a h

def cvalR (σ : K →+* ℂ) : CAt σ →+* ℂ := RingHom.id ℂ

def toCAt (σ : K →+* ℂ) (z : ℂ) : CAt σ := z

theorem cvalR_algebraMap (σ : K →+* ℂ) (t : K) : cvalR σ (algebraMap K (CAt σ) t) = σ t := rfl

theorem linIndep_alg_pts [CharZero K] {Kb : Type} [Field Kb] [IsAlgClosed Kb] [Algebra K Kb] [Normal K Kb] (p : TRing K) {m : ℕ} (a : Fin m → p.R)
    (ha : LinearIndependent K a) (v : Fin m → Kb)
    (h : ∀ φ : p.R →ₐ[K] Kb, ∑ i, v i * φ (a i) = 0) : v = 0 := by
  classical
  let L : IntermediateField K Kb := IntermediateField.adjoin K (Set.range v)
  haveI : FiniteDimensional K L :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  let u : Fin m → L := fun i => ⟨v i, IntermediateField.subset_adjoin K _ ⟨i, rfl⟩⟩
  have hu : ∀ i, algebraMap L Kb (u i) = v i := fun i => rfl

  have hg : ∀ (g : L →ₐ[K] Kb) (φ : p.R →ₐ[K] Kb), ∑ i, g (u i) * φ (a i) = 0 := by
    intro g φ
    let G : Kb →ₐ[K] Kb := g.liftNormal Kb
    have hb : Function.Bijective G := Algebra.IsAlgebraic.algHom_bijective G
    let Ge : Kb ≃ₐ[K] Kb := AlgEquiv.ofBijective G hb
    have h1 := h ((Ge.symm : Kb →ₐ[K] Kb).comp φ)
    have h2 := congrArg G h1
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum] at h2
    refine Eq.trans ?_ h2
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, ← hu i, AlgHom.liftNormal_commutes]
    congr 1
    show φ (a i) = G (Ge.symm (φ (a i)))
    exact (Ge.apply_symm_apply (φ (a i))).symm

  have htr : ∀ lam : L, ∀ i, Algebra.trace K L (lam * u i) = 0 := by
    intro lam
    have hpt : ∀ φ : p.R →ₐ[K] Kb, φ (∑ i, Algebra.trace K L (lam * u i) • a i) = 0 := by
      intro φ
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      have : ∀ i, φ (Algebra.trace K L (lam * u i) • a i) =
          (∑ g : L →ₐ[K] Kb, g (lam * u i)) * φ (a i) := by
        intro i
        rw [map_smul, Algebra.smul_def, ← trace_eq_sum_embeddings]
      simp_rw [this, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_eq_zero fun g _ => ?_
      have := hg g φ
      calc ∑ i, g (lam * u i) * φ (a i) = g lam * ∑ i, g (u i) * φ (a i) := by
            rw [Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; rw [map_mul, mul_assoc]
        _ = 0 := by rw [this, mul_zero]
    have h0 := eq_zero_of_pts p _ hpt
    exact fun i => (Fintype.linearIndependent_iff.1 ha _ h0) i
  funext i
  have hz : u i = 0 := by
    refine (traceForm_nondegenerate K L).1 (u i) fun lam => ?_
    rw [Algebra.traceForm_apply, mul_comm]
    exact htr lam i
  rw [← hu i, hz, map_zero]
  rfl

theorem linIndep_cpts [CharZero K] (σ : K →+* ℂ) (p : TRing K) {m : ℕ} (a : Fin m → p.R)
    (ha : LinearIndependent K a) (w : Fin m → ℂ)
    (h : ∀ ψ : p.R →ₐ[K] CAt σ, ∑ i, w i * cvalR σ (ψ (a i)) = 0) : w = 0 := by
  classical
  letI : Algebra K ℂ := σ.toAlgebra
  let ι : AlgebraicClosure K →ₐ[K] ℂ := (by
    refine @_root_.IsAlgClosed.lift _ _ _ _ _ _ _ _ _ _ _ ?_ ?_ ?_
    solve_by_elim* (maxDepth := 2) only [*,
      @_root_.DivisionSemiring.to_moduleIsTorsionFree,
      @_root_.Algebra.IsIntegral.isAlgebraic, @_root_.inferInstance])
  let Kb := AlgebraicClosure K
  letI : Module Kb ℂ := Module.compHom ℂ (ι.toRingHom : Kb →+* ℂ)
  have hsm : ∀ (c : Kb) (z : ℂ), c • z = ι c * z := fun _ _ => rfl
  by_contra hw
  obtain ⟨j, hj⟩ : ∃ j, w j ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hw (funext hne)
  obtain ⟨ℓ, hℓ⟩ : ∃ ℓ : Module.Dual Kb ℂ, ℓ (w j) ≠ 0 := by
    by_contra hne
    push Not at hne
    exact hj ((Module.forall_dual_apply_eq_zero_iff Kb (w j)).1 hne)
  have hv := linIndep_alg_pts (Kb := AlgebraicClosure K) p a ha (fun i => ℓ (w i)) fun φ => by
    have h1 := congrArg ℓ (h (ι.comp φ : p.R →ₐ[K] ℂ))
    set_option synthInstance.maxHeartbeats 100000 in
      rw [map_zero, map_sum] at h1
    refine Eq.trans ?_ h1
    refine Finset.sum_congr rfl fun i _ => ?_
    have e : w i * cvalR σ ((ι.comp φ : p.R →ₐ[K] ℂ) (a i)) = φ (a i) • w i := by
      rw [hsm, mul_comm]; rfl
    erw [e, map_smul, smul_eq_mul, mul_comm]
  exact hℓ (congrFun hv j)

theorem descend_cpts [CharZero K] (σ : K →+* ℂ) (p : TRing K) {r : ℕ} (a : Fin r → p.R) (w : Fin r → ℂ)
    (h : ∀ ψ : p.R →ₐ[K] CAt σ, ∑ j, w j * cvalR σ (ψ (a j)) = 0) (θ : Module.Dual K (CAt σ)) :
    ∑ j, θ (toCAt σ (w j)) • a j = 0 := by
  classical
  let S : Submodule K p.R := Submodule.span K (Set.range a)
  haveI : FiniteDimensional K S := FiniteDimensional.span_of_finite K (Set.finite_range a)
  let e := Module.finBasis K S
  let t : Fin r → Fin (Module.finrank K S) → K := fun j l => e.repr ⟨a j, Submodule.subset_span ⟨j, rfl⟩⟩ l
  have hat : ∀ j, a j = ∑ l, t j l • (e l : p.R) := by
    intro j
    have := e.sum_repr ⟨a j, Submodule.subset_span ⟨j, rfl⟩⟩
    have h2 := congrArg (fun x : S => (x : p.R)) this
    simp only [Submodule.coe_sum, Submodule.coe_smul] at h2
    exact h2.symm
  have hind : LinearIndependent K (fun l => (e l : p.R)) :=
    e.linearIndependent.map' S.subtype (Submodule.ker_subtype S)
  have key := linIndep_cpts σ p (fun l => (e l : p.R)) hind (fun l => ∑ j, σ (t j l) * w j) fun ψ => by
    rw [← h ψ]
    set_option synthInstance.maxHeartbeats 100000 in
      simp_rw [hat, map_sum, map_smul, Algebra.smul_def, map_mul, cvalR_algebraMap, Finset.mul_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun l _ => ?_
    ring
  have hk : ∀ l, ∑ j, t j l • toCAt σ (w j) = 0 := by
    intro l
    have := congrFun key l
    simp only [Pi.zero_apply] at this
    exact this
  calc ∑ j, θ (toCAt σ (w j)) • a j = ∑ l, θ (∑ j, t j l • toCAt σ (w j)) • (e l : p.R) := by
        set_option synthInstance.maxHeartbeats 100000 in
          simp_rw [hat, Finset.smul_sum, map_sum, map_smul, smul_eq_mul, Finset.sum_smul, smul_smul]
        rw [Finset.sum_comm]
        refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
        rw [mul_comm]
    _ = 0 := by simp [hk]

end Alg

end Formalism.L2.Pj
end
end

-- bundled from Formalism.LocalToGlobal.ProjectiveLattices.RhoWApply
section
noncomputable section

namespace Formalism.L2.Pj

section Act

variable {K : Type} [Field K] {ι : Type}
variable (pts : ∀ (S : Type) [CommRing S] [Algebra K S], Type)
variable (mapR : ∀ {S T : Type} [CommRing S] [Algebra K S] [CommRing T] [Algebra K T],
  (S →ₐ[K] T) → pts S → pts T → Prop)
variable (borR : ∀ {S : Type} [CommRing S] [Algebra K S], (ι → Sˣ) → pts S → pts S → Prop)
variable {G : Type} [Group G]
variable (actR : ∀ {S : Type} [CommRing S] [Algebra K S], G → pts S → pts S → Prop)

def mvPt (g : G) {S : Type} [CommRing S] [Algebra K S] (y : pts S) : pts S :=
  open Classical in if h : ∃ y', actR g y y' then h.choose else y

def actRule (g : G) (f : Rules pts) : Rules pts := fun p y => f p (mvPt pts actR g y)

def actL (g : G) : Rules pts →ₗ[K] Rules pts where
  toFun := actRule pts actR g
  map_add' _ _ := rfl
  map_smul' _ _ := rfl

theorem actL_apply (g : G) (f : Rules pts) (p : TRing K) (y : pts p.R) :
    actL pts actR g f p y = f p (mvPt pts actR g y) := rfl

def ActTotal : Prop :=
  ∀ (g : G) (S : Type) [CommRing S] [Algebra K S] (y : pts S), ∃ y', actR g y y'

def ActFun : Prop :=
  ∀ (g : G) (S : Type) [CommRing S] [Algebra K S] (y y' y'' : pts S),
    actR g y y' → actR g y y'' → mapR (AlgHom.id K S) y' y''

def ActOne : Prop :=
  ∀ (S : Type) [CommRing S] [Algebra K S] (y : pts S), actR 1 y y

def ActMul : Prop :=
  ∀ (g h : G) (S : Type) [CommRing S] [Algebra K S] (y y' y'' : pts S),
    actR g y y' → actR h y' y'' → actR (g * h) y y''

def ActNat : Prop :=
  ∀ (g : G) (S T : Type) [CommRing S] [Algebra K S] [CommRing T] [Algebra K T] (φ : S →ₐ[K] T)
    (y y' : pts S) (z z' : pts T), mapR φ y z → actR g y y' → actR g z z' → mapR φ y' z'

def ActBor : Prop :=
  ∀ (g : G) (S : Type) [CommRing S] [Algebra K S] (t : ι → Sˣ) (y y' z z' : pts S),
    borR t y z → actR g y y' → actR g z z' → borR t y' z'

variable {pts actR}

theorem mvPt_spec (hT : ActTotal pts actR) (g : G) {S : Type} [CommRing S] [Algebra K S] (y : pts S) :
    actR g y (mvPt pts actR g y) := by
  have h := hT g S y
  unfold mvPt
  rw [dite_eq_left h]
  exact h.choose_spec

variable (pts actR)

theorem actL_mem [Fintype ι] (hT : ActTotal pts actR) (hN : ActNat pts mapR actR) (hB : ActBor pts borR actR)
    (e : ι → ℕ) (g : G) {f : Rules pts} (hf : f ∈ secW pts mapR borR e) :
    actL pts actR g f ∈ secW pts mapR borR e := by
  obtain ⟨h1, h2⟩ := hf
  refine ⟨?_, ?_⟩
  · intro p q φ y z hyz
    exact h1 p q φ _ _ (hN g p.R q.R φ y (mvPt pts actR g y) z (mvPt pts actR g z) hyz
      (mvPt_spec hT g y) (mvPt_spec hT g z))
  · intro p t y y' hyy
    exact h2 p t _ _ (hB g p.R t y (mvPt pts actR g y) y' (mvPt pts actR g y') hyy
      (mvPt_spec hT g y) (mvPt_spec hT g y'))

theorem actL_one (hT : ActTotal pts actR) (hF : ActFun pts mapR actR) (hO : ActOne pts actR)
    {f : Rules pts} (hf : IsNatural pts mapR f) : actL pts actR 1 f = f := by
  funext p y
  show f p (mvPt pts actR 1 y) = f p y
  exact hf p p (AlgHom.id K p.R) y _ (hF 1 p.R y y _ (hO p.R y) (mvPt_spec hT 1 y))

theorem actL_mul (hT : ActTotal pts actR) (hF : ActFun pts mapR actR) (hM : ActMul pts actR)
    (g h : G) {f : Rules pts} (hf : IsNatural pts mapR f) :
    actL pts actR (g * h) f = actL pts actR g (actL pts actR h f) := by
  funext p y
  show f p (mvPt pts actR (g * h) y) = f p (mvPt pts actR h (mvPt pts actR g y))
  have h1 : actR (g * h) y (mvPt pts actR h (mvPt pts actR g y)) :=
    hM g h p.R y _ _ (mvPt_spec hT g y) (mvPt_spec hT h _)
  exact (hf p p (AlgHom.id K p.R) _ _ (hF (g * h) p.R y _ _ (mvPt_spec hT (g * h) y) h1)).symm

structure ActLaws : Prop where
  total : ActTotal pts actR
  func : ActFun pts mapR actR
  one : ActOne pts actR
  mul : ActMul pts actR
  nat : ActNat pts mapR actR
  bor : ActBor pts borR actR

variable {pts mapR borR actR}

end Act

end Formalism.L2.Pj
end
end

