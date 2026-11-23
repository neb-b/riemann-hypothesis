module

public import Mathlib
public import Formalism.LocalToGlobal.Columns.FiniteSumNonzeroLargeDepth
public import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0050
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.Bundle0054
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.LevelPrimeIncidenceFiniteFibresStable

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.TwistPrimeDatumIntegralSupportAndInvariant
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col GlobalTheory.QNormal

noncomputable section

namespace GlobalTheory.Proof.twistPrimeDatum_integral_support_and_invariant

variable {E : Type} [Field E] [NumberField E]

theorem entB_zero (q : ℕ) {N' N : ℕ} (k₀ c' n' c n : ℕ) (x : (Fin N' → E) →ₗ[E] (Fin N → E)) (p p' : ℕ) :
    LocE.entB q k₀ c' n' c n 0 0 x p p' =
      Loc.atN (x (Loc.eN E N' (LocE.fIdx k₀ c' n' p'))) (LocE.fIdx k₀ c n p) := by
  simp [LocE.entB, LocE.scE]

theorem intAt_entB {P : HeightOneSpectrum (𝓞 E)} (q : ℕ) {N' N : ℕ} (k₀ c' n' c n : ℕ)
    {y : (Fin N' → E) →ₗ[E] (Fin N → E)} (hy : IntHom P y) (p p' : ℕ) :
    IntAt P (LocE.entB q k₀ c' n' c n 0 0 y p p') := by
  rw [entB_zero]
  have h : IntV P (Loc.eN E N' (LocE.fIdx k₀ c' n' p')) := fun l => by
    unfold Loc.eN
    split_ifs
    · exact intAt_one P
    · exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P
  unfold Loc.atN
  split_ifs
  · exact hy _ h _
  · exact IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_zero P

theorem entB_add (q : ℕ) {N' N : ℕ} (k₀ c' n' c n : ℕ) (x y : (Fin N' → E) →ₗ[E] (Fin N → E)) (a : E) (p p' : ℕ) :
    LocE.entB q k₀ c' n' c n 0 0 (x + a • y) p p' =
      LocE.entB q k₀ c' n' c n 0 0 x p p' + a * LocE.entB q k₀ c' n' c n 0 0 y p p' := by
  rw [entB_zero, entB_zero, entB_zero, LinearMap.add_apply, LinearMap.smul_apply, atN_add, atN_smul]

theorem fIdx_fPos {k₀ c n l : ℕ} (hk : k₀ ≤ n) (hl : l < n + c) :
    LocE.fIdx k₀ c n (LocE.fPos k₀ c n l) = l ∧ LocE.fPos k₀ c n l < n + c := by
  unfold LocE.fIdx LocE.fPos
  split_ifs <;> omega

theorem unitV_congr {K : Type} [Field K] {P : HeightOneSpectrum (𝓞 E)} (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a b : E}
    (h : redP P a = redP P b) : LocE.unitV ξ a = LocE.unitV ξ b := by
  unfold LocE.unitV
  have key : ∀ u v : 𝓞 E ⧸ P.asIdeal, u = v →
      (open Classical in if h : IsUnit u then ((ξ h.unit : Kˣ) : K) else 0) =
        (open Classical in if h : IsUnit v then ((ξ h.unit : Kˣ) : K) else 0) := by
    rintro u v rfl
    rfl
  exact key _ _ h

theorem intAt_add_iff {P : HeightOneSpectrum (𝓞 E)} {a b : E} (hb : IntAt P b) : IntAt P (a + b) ↔ IntAt P a :=
  ⟨fun h => by simpa using h.add (IndefiniteRowSideFullHecke.SourceLatticeInvariance.intAt_neg hb), fun h => h.add hb⟩

theorem phiQ_bdd : ∀ (E : Type) [Field E] [NumberField E] (K : Type) [Field K] (P : HeightOneSpectrum (𝓞 E)) (ξ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) (k₀ r c' n' c n : ℕ), k₀ ≤ n' → k₀ ≤ n → r ≤ n' + c' → r ≤ n + c → (∀ x, LocE.PhiQ (qOf P) ξ k₀ r c' n' c n x ≠ 0 → IntHom P x) ∧ ∀ x y : (Fin (n' + c') → E) →ₗ[E] (Fin (n + c) → E), IntHom P y → LocE.PhiQ (qOf P) ξ k₀ r c' n' c n (x + (qOf P : E) • y) = LocE.PhiQ (qOf P) ξ k₀ r c' n' c n x := by
  intro E _ _ K _ P ξ k₀ r c' n' c n hk' hk hr' hr
  refine ⟨fun x hx => ?_, fun x y hy => ?_⟩
  · unfold LocE.PhiQ at hx
    split_ifs at hx with h
    · rw [intHom_iff]
      intro s l
      obtain ⟨a1, a2⟩ := fIdx_fPos hk l.2
      obtain ⟨b1, b2⟩ := fIdx_fPos hk' s.2
      have := h.1 _ _ a2 b2
      rw [entB_zero, a1, b1] at this
      have e : Loc.eN E (n' + c') s.1 = Pi.single s 1 := by
        funext i
        simp [Loc.eN, Pi.single_apply, Fin.ext_iff]
      rw [e] at this
      simpa [Loc.atN] using this
    · exact absurd rfl hx
  · have hq : (qOf P : E) ≠ 0 := NormalFormAtPrime.qOf_ne_zero P
    have hI := intAt_entB (qOf P) k₀ c' n' c n hy
    have e1 : ∀ p p', IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 (x + (qOf P : E) • y) p p') ↔
        IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x p p') := fun p p' => by
      rw [entB_add, intAt_add_iff ((TopStep.intAt_nat (qOf P)).mul (hI p p'))]
    have e2 : ∀ p p', IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 (x + (qOf P : E) • y) p p' / (qOf P : E)) ↔
        IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x p p' / (qOf P : E)) := fun p p' => by
      rw [entB_add, add_div, mul_div_cancel_left₀ _ hq, intAt_add_iff (hI p p')]
    unfold LocE.PhiQ
    split_ifs with h' h h
    rotate_left
    · exact absurd ⟨fun p p' a b => (e1 p p').1 (h'.1 p p' a b), fun p p' a b d => (e2 p p').1 (h'.2 p p' a b d)⟩ h
    · exact absurd ⟨fun p p' a b => (e1 p p').2 (h.1 p p' a b), fun p p' a b d => (e2 p p').2 (h.2 p p' a b d)⟩ h'
    · rfl
    · apply unitV_congr
      have hx : ∀ s t : Fin r, IntAt P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x s.1 t.1) :=
        fun s t => h.1 _ _ (by have := s.2; omega) (by have := t.2; omega)
      refine (TopStep.det_int ?_).2.trans (Eq.trans ?_ (TopStep.det_int ?_).2.symm)
      · exact fun s t => (e1 _ _).2 (hx s t)
      swap
      · exact hx
      refine congrArg Matrix.det (Matrix.ext fun s t => ?_)
      change redP P (LocE.entB (qOf P) k₀ c' n' c n 0 0 (x + (qOf P : E) • y) s.1 t.1) =
        redP P (LocE.entB (qOf P) k₀ c' n' c n 0 0 x s.1 t.1)
      rw [entB_add, reduction_add (hx s t) ((TopStep.intAt_nat (qOf P)).mul (hI _ _)), reduction_mul (TopStep.intAt_nat (qOf P)) (hI _ _), TopStep.reduction_absNorm_eq_zero, zero_mul, add_zero]

end GlobalTheory.Proof.twistPrimeDatum_integral_support_and_invariant
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.UopIsExt
section
noncomputable section

namespace GlobalTheory.LvT

open Formalism.BasicNotions Classical NumberField
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw)

namespace LocF

variable {q : ℕ} {F : Type} [Field F] {Lc : LocF q F} {n : ℕ}

theorem uext_mem_std (x : Fin n → Lc.K) : x ∈ Lc.std n ↔ ∀ a, x a ∈ Lc.O := by
  simp only [std, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  refine forall_congr' fun a => ⟨?_, fun h => ⟨⟨x a, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]; exact y.2

theorem uext_ker {Λ : Submodule Lc.O (Fin n → Lc.K)} {h : GL (Fin n) Lc.K} (hh : Lc.IsFrame n h Λ)
    {V : Type*} [AddCommGroup V] [Module F V] (hV : Module.finrank F V = n) (π : (Fin n → Lc.K) → V)
    (hadd : ∀ x ∈ Λ, ∀ y ∈ Λ, π (x + y) = π x + π y)
    (hsmul : ∀ (a : Lc.O), ∀ x ∈ Λ, π (a • x) = Lc.res a • π x)
    (hsurj : ∀ y, ∃ x ∈ Λ, π x = y) {x : Fin n → Lc.K} (hx : x ∈ Λ) (h0 : π x = 0) :
    ((q : Lc.K))⁻¹ • x ∈ Λ := by
  let π' : Λ →+ V := AddMonoidHom.mk' (fun x => π x) (fun x y => hadd x x.2 y y.2)
  have hb : ∀ a : Fin n, Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) (Pi.single a 1) ∈ Λ := by
    intro a
    rw [hh, uext_mem_std]
    intro b
    by_cases hab : b = a
    · subst hab; simp
    · simp [Pi.single_eq_of_ne hab]
  let b : Fin n → Λ := fun a => ⟨_, hb a⟩
  have key : ∀ x ∈ Λ, ∃ z : Fin n → Lc.O,
      x = Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) (fun a => (z a : Lc.K)) ∧
      π x = ∑ a, Lc.res (z a) • π (b a) := by
    intro x hx
    have e1 : Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K)
        (Matrix.mulVec ((h⁻¹ : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) x) = x := by
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    have e2 := (uext_mem_std _).1 ((hh _).1 (e1.symm ▸ hx))
    let z : Fin n → Lc.O := fun a => ⟨_, e2 a⟩
    have e0 : x = Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) (fun a => (z a : Lc.K)) := e1.symm
    refine ⟨z, e0, ?_⟩
    have e3 : (⟨x, hx⟩ : Λ) = ∑ a, z a • b a := by
      apply Subtype.ext
      rw [Submodule.coe_sum]
      change x = ∑ a, (z a : Lc.K) • Matrix.mulVec (h : Matrix (Fin n) (Fin n) Lc.K) (Pi.single a 1)
      simp only [← Matrix.mulVec_smul]
      rw [← Matrix.mulVec_sum, e0]
      congr 1
      ext c
      simp [Finset.sum_apply, Pi.single_apply]
    have e4 : π x = π' ⟨x, hx⟩ := rfl
    set_option synthInstance.maxHeartbeats 100000 in
      rw [e4, e3, map_sum]
    exact Finset.sum_congr rfl fun a _ => hsmul (z a) _ (b a).2
  have hli : LinearIndependent F (fun a => π (b a)) := by
    apply linearIndependent_of_top_le_span_of_card_eq_finrank
    · intro y _
      obtain ⟨x, hx, rfl⟩ := hsurj y
      obtain ⟨z, -, hz⟩ := key x hx
      rw [hz]
      exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)
    · simp [hV]
  obtain ⟨z, hz1, hz2⟩ := key x hx
  have hz3 := Fintype.linearIndependent_iff.1 hli (fun a => Lc.res (z a)) (by rw [← hz2, h0])
  rw [hz1, ← Matrix.mulVec_smul, hh, uext_mem_std]
  intro a
  obtain ⟨y, hy⟩ := (Lc.res_ker _).1 (hz3 a)
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hy, ← mul_assoc, inv_mul_cancel₀ Lc.q_ne, one_mul]
  exact y.2

theorem uext_mem_of_ne (p : PP Lc n) {x : Fin n → Lc.K} (hx : p.1.f x = 1) : x ∈ p.1.L := by
  by_contra h
  exact one_ne_zero (hx.symm.trans (p.2.off x h))

theorem uext_sub_mem {p p₁ : PP Lc n} {x y : Fin n → Lc.K} (hx : p.IsUp x p₁) (hy : p.IsUp y p₁) :
    ((q : Lc.K))⁻¹ • (x - y) ∈ p.1.L := by
  have h1 := uext_mem_of_ne p₁ hx.2.2
  have h2 := uext_mem_of_ne p₁ hy.2.2
  have h3 : ((q : Lc.K))⁻¹ • (x - y) ∈ p₁.1.L := by rw [smul_sub]; exact p₁.1.L.sub_mem h1 h2
  have h4 := p₁.2.add _ h3 _ h2
  rw [← smul_add, sub_add_cancel, hx.2.2, hy.2.2] at h4
  have h5 : ((q : Lc.K))⁻¹ • (x - y) ∈ p₁.ker := ⟨h3, by linear_combination -h4⟩
  rw [hx.2.1] at h5
  exact h5

theorem uext_isUp_of_sub {p p₁ : PP Lc n} {x y : Fin n → Lc.K} (hy : p.IsUp y p₁) (hx : x ∈ p.1.L)
    (hxy : ((q : Lc.K))⁻¹ • (x - y) ∈ p.1.L) : p.IsUp x p₁ := by
  refine ⟨hx, hy.2.1, ?_⟩
  have h2 := uext_mem_of_ne p₁ hy.2.2
  have h5 : ((q : Lc.K))⁻¹ • (x - y) ∈ p₁.ker := by rw [hy.2.1]; exact hxy
  have h4 := p₁.2.add _ h5.1 _ h2
  rw [← smul_add, sub_add_cancel, hy.2.2, h5.2, zero_add] at h4
  exact h4

end LocF

variable {D : D7} {u : D.what₂.Word} {X : Ch D u} {i : ℕ} (M : PtModel X i)

theorem PtModel.uext_piL_eq_iff (v : X.A.vT) (c : X.C.cls i) {x y : Fin (D.R.N i) → (M.Lc v).K}
    (hx : x ∈ ((M.rep c).2 v).1.L) (hy : y ∈ ((M.rep c).2 v).1.L) :
    M.piL v c x = M.piL v c y ↔ ((X.A.T : (M.Lc v).K))⁻¹ • (x - y) ∈ ((M.rep c).2 v).1.L := by
  have hxy := Submodule.sub_mem _ hx hy
  have e := M.piL_add v c _ hxy _ hy
  rw [sub_add_cancel] at e
  constructor
  · intro h
    obtain ⟨f, hf⟩ := ((M.rep c).2 v).2.lat
    refine LocF.uext_ker hf (X.fm.lv_rank i v c) (M.piL v c) (M.piL_add v c) (M.piL_smul v c) (M.piL_surj v c) hxy ?_
    rw [h] at e
    simpa using e
  · intro h
    have e2 := M.piL_smul v c (X.A.T : (M.Lc v).O) _ h
    have e3 : (M.Lc v).res (X.A.T : (M.Lc v).O) = 0 := ((M.Lc v).res_ker _).2 ⟨1, by simp⟩
    rw [e3, zero_smul, Subring.smul_def, smul_smul, Subring.coe_natCast, mul_inv_cancel₀ (M.Lc v).q_ne, one_smul] at e2
    rw [e, e2, zero_add]

theorem uop_isExt : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (v : X.A.vT) (φ : Fn X i)
    (Φ : M.Pt → M.Val), M.IsExt φ Φ → M.IsExt (Uop X i v φ) (fun p => ∑ᶠ p₁ ∈ {p₁ | M.Inc v p p₁}, Φ p₁) := by
  intro D u X i M v φ Φ hΦ
  obtain ⟨hfin, hact, huniq⟩ := _root_.GlobalTheory.LvT.inc_finite_stable D u X i M v
  constructor
  · intro c
    choose s hs1 hs2 using M.piL_surj v c
    have hf : ∀ y, X.fm.fv i v c y = 1 → ((M.rep c).2 v).1.f (s y) = 1 := by
      intro y hy
      rw [← M.piL_f v c _ (hs1 y), hs2, hy]
    let t : X.fm.lv i v c → LocF.PP (M.Lc v) (D.R.N i) := fun y =>
      if hy : X.fm.fv i v c y = 1 then (huniq (M.rep c) _ (hf y hy)).exists.choose else (M.rep c).2 v
    have ht : ∀ y, X.fm.fv i v c y = 1 → ((M.rep c).2 v).IsUp (s y) (t y) := by
      intro y hy
      simp only [t, dif_pos hy]
      exact (huniq (M.rep c) _ (hf y hy)).exists.choose_spec
    let P : X.fm.lv i v c → M.Pt := fun y => ((M.rep c).1, Function.update (M.rep c).2 v (t y))
    have hbij : Set.BijOn P
        ((Finset.univ.filter (fun x : X.fm.lv i v c => X.fm.fv i v c x = 1) : Finset _) : Set _)
        {p₁ | M.Inc v (M.rep c) p₁} := by
      refine ⟨?_, ?_, ?_⟩
      · intro y hy
        have hy' : X.fm.fv i v c y = 1 := by simpa using hy
        refine ⟨rfl, fun v' hv' => Function.update_of_ne hv' _ _, s y, hf y hy', ?_⟩
        simp only [P, Function.update_self]
        exact ht y hy'
      · intro y hy y' hy' e
        have h1 : X.fm.fv i v c y = 1 := by simpa using hy
        have h2 : X.fm.fv i v c y' = 1 := by simpa using hy'
        have e1 : t y = t y' := by
          have := congrFun (congrArg Prod.snd e) v
          simpa only [P, Function.update_self] using this
        have h3 := LocF.uext_sub_mem (ht y h1) (e1 ▸ ht y' h2)
        rw [← hs2 y, ← hs2 y']
        exact (M.uext_piL_eq_iff v c (hs1 y) (hs1 y')).2 h3
      · rintro p₁ ⟨h1, h2, x, hx1, hx2⟩
        have hy : X.fm.fv i v c (M.piL v c x) = 1 := by rw [M.piL_f v c x hx2.1, hx1]
        refine ⟨M.piL v c x, by simpa using hy, ?_⟩
        have h3 := LocF.uext_isUp_of_sub hx2 (hs1 _)
          ((M.uext_piL_eq_iff v c (hs1 _) hx2.1).1 (hs2 _))
        have h4 := (huniq (M.rep c) _ (hf _ hy)).unique (ht _ hy) h3
        refine Prod.ext h1.symm (funext fun v' => ?_)
        by_cases hv : v' = v
        · subst hv
          simp only [P, Function.update_self]
          exact h4
        · simp only [P, Function.update_of_ne hv]
          exact (h2 v' hv).symm
    have e1 := finsum_mem_eq_of_bijOn (f := fun y => Φ (P y)) (g := Φ) P hbij (fun _ _ => rfl)
    beta_reduce
    rw [← e1, finsum_mem_coe_finset, Submodule.coe_sum]
    simp only [Uop, LinearMap.pi_apply, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply,
      LinearEquiv.coe_coe]
    refine Finset.sum_congr rfl fun y hy => ?_
    have hy' : X.fm.fv i v c y = 1 := by simpa using hy
    obtain ⟨g, hg1, hg2⟩ := M.up_eq v c (s y) (t y) (hf y hy') (ht y hy')
    rw [hs2] at hg1 hg2
    rw [hΦ.1, hg2, ← hΦ.2, hg1]
  · intro g p
    have hbij : Set.BijOn (fun p₁ : M.Pt => g • p₁) {p₁ | M.Inc v p p₁} {p₁ | M.Inc v (g • p) p₁} := by
      refine ⟨fun p₁ h => (hact g p p₁).1 h, fun a _ b _ e => MulAction.injective g e, fun p₁ h => ?_⟩
      refine ⟨g⁻¹ • p₁, (hact g p _).2 ?_, smul_inv_smul g p₁⟩
      rw [smul_inv_smul]; exact h
    have e1 := finsum_mem_eq_of_bijOn (f := fun p₁ => M.act g (Φ p₁)) (g := Φ) _ hbij (fun a _ => (hΦ.2 g a).symm)
    beta_reduce
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← e1, finsum_mem_eq_finite_toFinset_sum _ (hfin p).1, finsum_mem_eq_finite_toFinset_sum _ (hfin p).1, map_sum]

end GlobalTheory.LvT
end
end

