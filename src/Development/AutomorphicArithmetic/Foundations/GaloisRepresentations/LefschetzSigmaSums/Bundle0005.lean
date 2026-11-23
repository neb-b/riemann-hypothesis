module

public import Mathlib
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.Bundle0004
public import Formalism.SatakeDualWeyl.Statement
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0004
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsLevelEqKN

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PAltLin
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory GlobalTheory.HodgeCoh

namespace UpperTheory.Gal.LocalSmoothExtension

private theorem trace_comb {M : Type*} [AddCommGroup M] [Module ℂ M] {m : ℕ} {A : Type*}
    (u : Fin m → Module.End ℂ M) (c : Fin m → ℂ) (w : A →₀ ℂ) (e : A → Module.End ℂ M) :
    LinearMap.trace ℂ M ((∑ i, c i • u i) ∘ₗ w.sum fun α r => r • e α) =
      ∑ i, c i * w.sum fun α r => r * LinearMap.trace ℂ M (u i ∘ₗ e α) := by
  set_option synthInstance.maxHeartbeats 100000 in
    simp only [Finsupp.sum, ← Module.End.mul_eq_comp, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc,
    mul_smul_comm, map_sum, map_smul, smul_eq_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun α _ => ?_
  ring

private theorem sum_rearrange {m : ℕ} {A : Type*} (R : Finset ℕ) (S : Finset A) (c : Fin m → ℂ) (w : A → ℂ)
    (x z : ℕ → ℂ) (t : Fin m → A → ℕ → ℕ → ℂ) :
    ∑ a ∈ R, x a * ∑ b ∈ R, z b * ∑ i, c i * ∑ α ∈ S, w α * t i α a b =
      ∑ i, c i * ∑ α ∈ S, w α * ∑ a ∈ R, x a * ∑ b ∈ R, z b * t i α a b := by
  simp only [Finset.mul_sum]
  calc _ = ∑ a ∈ R, ∑ i, ∑ b ∈ R, ∑ α ∈ S, x a * (z b * (c i * (w α * t i α a b))) :=
        Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ a ∈ R, ∑ b ∈ R, ∑ α ∈ S, x a * (z b * (c i * (w α * t i α a b))) := Finset.sum_comm
    _ = ∑ i, ∑ a ∈ R, ∑ α ∈ S, ∑ b ∈ R, x a * (z b * (c i * (w α * t i α a b))) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun a _ => Finset.sum_comm
    _ = ∑ i, ∑ α ∈ S, ∑ a ∈ R, ∑ b ∈ R, x a * (z b * (c i * (w α * t i α a b))) :=
        Finset.sum_congr rfl fun i _ => Finset.sum_comm
    _ = _ := by
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun α _ =>
          Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
        ring

private theorem alt_family {M : ℕ → ℕ → Type*} [∀ a b, AddCommGroup (M a b)] [∀ a b, Module ℂ (M a b)]
    (d m : ℕ) {A : Type*} (u : Fin m → ∀ a b : ℕ, Module.End ℂ (M a b)) (c : Fin m → ℂ) (w : A →₀ ℂ)
    (e : A → ∀ a b : ℕ, Module.End ℂ (M a b)) (y : ℂ) :
    ∑ a ∈ Finset.range (d + 1), (-y) ^ a * ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b *
        LinearMap.trace ℂ (M a b) ((∑ i, c i • u i a b) ∘ₗ w.sum fun α r => r • e α a b) =
      ∑ i, c i * w.sum fun α r => r * ∑ a ∈ Finset.range (d + 1), (-y) ^ a *
        ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b * LinearMap.trace ℂ (M a b) (u i a b ∘ₗ e α a b) := by
  simp only [trace_comb]
  simp only [Finsupp.sum]
  exact sum_rearrange (Finset.range (d + 1)) w.support c (fun α => w α) (fun a => (-y) ^ a) (fun b => (-1 : ℂ) ^ b)
    fun i α a b => LinearMap.trace ℂ (M a b) (u i a b ∘ₗ e α a b)

theorem altLin_of : AltLin := fun Z s d m A u c w e y =>
  alt_family (M := fun a b => hodgeH s a b) d m u c w e y

end UpperTheory.Gal.LocalSmoothExtension
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PFnDecomp
section
set_option autoImplicit false

noncomputable section

namespace UpperTheory.Gal.LocalSmoothExtension.FunctionDecomposition

variable {H : Type} [Group H] {K : Subgroup H} {f : H → ℂ}

private lemma val_of_mem (hb : ∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) {g x : H}
    (hg : g ∈ DoubleCoset.doubleCoset x (K : Set H) K) : f g = f x := by
  obtain ⟨a, ha, b, hb', rfl⟩ := DoubleCoset.mem_doubleCoset.1 hg
  rw [(hb b hb' _).2, (hb a ha _).1]

private lemma ind_mem {g x : H} (hg : g ∈ DoubleCoset.doubleCoset x (K : Set H) K) :
    UpperTheory.Gal.G3.ind ℂ K x g = 1 :=
  Set.indicator_of_mem hg _

private lemma ind_notMem {g x : H} (hg : g ∉ DoubleCoset.doubleCoset x (K : Set H) K) :
    UpperTheory.Gal.G3.ind ℂ K x g = 0 :=
  Set.indicator_of_notMem hg _

private lemma mem_of_ind {g x : H} (hg : UpperTheory.Gal.G3.ind ℂ K x g ≠ 0) :
    g ∈ DoubleCoset.doubleCoset x (K : Set H) K := by
  by_contra hn
  exact hg (ind_notMem hn)

private lemma mk_of_mem {g : H} {q : DoubleCoset.Quotient (K : Set H) K}
    (hg : g ∈ DoubleCoset.doubleCoset q.out (K : Set H) K) : DoubleCoset.mk K K g = q :=
  (DoubleCoset.mem_quotToDoubleCoset_iff q g).1 hg

private lemma mem_of_mk {g : H} {q : DoubleCoset.Quotient (K : Set H) K}
    (hg : DoubleCoset.mk K K g = q) : g ∈ DoubleCoset.doubleCoset q.out (K : Set H) K :=
  (DoubleCoset.mem_quotToDoubleCoset_iff q g).2 hg

private lemma coset_ne (hb : ∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g) {g : H} (hg : f g ≠ 0) :
    (g : H ⧸ K) ∈ {y : H ⧸ K | f y.out ≠ 0} := by
  obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K g
  show f (g : H ⧸ K).out ≠ 0
  rw [hc, (hb c c.2 g).2]
  exact hg

private lemma mem_hecke (hb : ∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g)
    (hfin : {y : H ⧸ K | f y.out ≠ 0}.Finite) : f ∈ Formalism.UG.Hecke ℂ K := by
  classical
  have h : Formalism.UG.IsBiInv K f ∧ Formalism.UG.FinDosetSupp K f := by
    refine ⟨fun a b g => ?_, hfin.toFinset.image Quotient.out, fun g hg => ?_⟩
    · rw [(hb b b.2 _).2, (hb a a.2 _).1]
    · obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K g
      refine ⟨(g : H ⧸ K).out, Finset.mem_image.2 ⟨_, hfin.mem_toFinset.2 (coset_ne hb hg), rfl⟩, 1, c⁻¹, ?_⟩
      rw [hc]
      simp
  exact h

private lemma decomp (hb : ∀ k ∈ K, ∀ g, f (k * g) = f g ∧ f (g * k) = f g)
    (hfin : {y : H ⧸ K | f y.out ≠ 0}.Finite) :
    ∃ (m : ℕ) (q : Fin m → H) (c : Fin m → ℂ), (∀ i, f (q i) ≠ 0) ∧
      f = ∑ i, c i • UpperTheory.Gal.G3.ind ℂ K (q i) ∧ ∀ i g, UpperTheory.Gal.G3.ind ℂ K (q i) g ≠ 0 → f g ≠ 0 := by
  classical
  let Q : Finset (DoubleCoset.Quotient (K : Set H) K) :=
    (hfin.toFinset.image fun y => DoubleCoset.mk K K y.out).filter fun q => f q.out ≠ 0
  have hQ : ∀ q : DoubleCoset.Quotient (K : Set H) K, f q.out ≠ 0 → q ∈ Q := by
    intro q hq
    refine Finset.mem_filter.2 ⟨Finset.mem_image.2 ⟨(q.out : H ⧸ K), hfin.mem_toFinset.2 (coset_ne hb hq), ?_⟩, hq⟩
    obtain ⟨c, hc⟩ := QuotientGroup.mk_out_eq_mul K q.out
    refine mk_of_mem (DoubleCoset.mem_doubleCoset.2 ⟨1, K.one_mem, c, c.2, ?_⟩)
    rw [hc]
    simp
  have hne : ∀ q ∈ Q, f q.out ≠ 0 := fun q hq => (Finset.mem_filter.1 hq).2
  let e := Q.equivFin
  refine ⟨Q.card, fun i => (e.symm i).1.out, fun i => f (e.symm i).1.out, fun i => hne _ (e.symm i).2, ?_, ?_⟩
  · funext g
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hg : f g = 0
    · rw [hg]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      rw [ind_notMem fun hm => hne _ (e.symm i).2 (by rw [← val_of_mem hb hm]; exact hg), mul_zero]
    · have hp : f (DoubleCoset.mk K K g).out = f g :=
        val_of_mem hb (by
          obtain ⟨a, ha, b, hb', e'⟩ := DoubleCoset.mk_out_eq_mul K K g
          exact DoubleCoset.mem_doubleCoset.2 ⟨a, ha, b, hb', e'⟩)
      have hpQ := hQ (DoubleCoset.mk K K g) (by rw [hp]; exact hg)
      rw [Finset.sum_eq_single (e ⟨_, hpQ⟩)]
      · rw [e.symm_apply_apply]
        show f g = f (DoubleCoset.mk K K g).out * _
        rw [ind_mem (mem_of_mk rfl), hp, mul_one]
      · intro i _ hi
        rw [ind_notMem, mul_zero]
        intro hm
        apply hi
        have : (⟨_, hpQ⟩ : Q) = e.symm i := Subtype.ext (mk_of_mem hm)
        rw [this, e.apply_symm_apply]
      · intro h
        exact absurd (Finset.mem_univ _) h
  · intro i g hg
    rw [val_of_mem hb (mem_of_ind hg)]
    exact hne _ (e.symm i).2

end UpperTheory.Gal.LocalSmoothExtension.FunctionDecomposition

open UpperTheory.Gal.LocalSmoothExtension.FunctionDecomposition in
private theorem UpperTheory.Gal.LocalSmoothExtension.FunctionDecomposition.fwd {B : AlgebraicGeometry.Scheme.{0}} {Γ : Type} [Group Γ]
    (X : UpperTheory.Gal.G3.Tower B Γ) (j : X.ι) (f : Γ → ℂ) (hf : X.IsFn j f) :
    f ∈ Formalism.UG.Hecke ℂ (X.K j) ∧ ∃ (m : ℕ) (h : Fin m → Γ) (c : Fin m → ℂ), (∀ i, h i ∈ X.Δ) ∧
      f = ∑ i, c i • UpperTheory.Gal.G3.ind ℂ (X.K j) (h i)⁻¹ ∧
      ∀ i g, UpperTheory.Gal.G3.ind ℂ (X.K j) (h i)⁻¹ g ≠ 0 → f g ≠ 0 := by
  obtain ⟨hb, hΔ, hfin⟩ := hf
  obtain ⟨m, q, c, hq, e, hs⟩ := decomp hb hfin
  refine ⟨mem_hecke hb hfin, m, fun i => (q i)⁻¹, c, fun i => hΔ _ (hq i), ?_, ?_⟩
  · simpa only [inv_inv] using e
  · simpa only [inv_inv] using hs

private theorem UpperTheory.Gal.LocalSmoothExtension.FunctionDecomposition.bwd {B : AlgebraicGeometry.Scheme.{0}} {Γ : Type} [Group Γ]
    (X : UpperTheory.Gal.G3.Tower B Γ) (j : X.ι) (f : Γ → ℂ) (hf : f ∈ Formalism.UG.Hecke ℂ (X.K j))
    (hΔ : ∀ g, f g ≠ 0 → g⁻¹ ∈ X.Δ) : X.IsFn j f := by
  classical
  obtain ⟨hb, S, hS⟩ : Formalism.UG.IsBiInv (X.K j) f ∧ Formalism.UG.FinDosetSupp (X.K j) f := hf
  have hbi : ∀ k ∈ X.K j, ∀ g, f (k * g) = f g ∧ f (g * k) = f g := fun k hk g =>
    ⟨by simpa using hb ⟨k, hk⟩ 1 g, by simpa using hb 1 ⟨k, hk⟩ g⟩
  refine ⟨hbi, hΔ, ?_⟩
  have hone : ∀ s : Γ, s⁻¹ ∈ X.Δ →
      {y : Γ ⧸ X.K j | UpperTheory.Gal.G3.ind ℂ (X.K j) s y.out ≠ 0}.Finite := by
    intro s hs
    have := ((UpperTheory.Gal.G3.pFnRing X ℂ j).1 s⁻¹ hs).2.2
    simpa only [inv_inv] using this
  refine ((S.filter fun s => s⁻¹ ∈ X.Δ).finite_toSet.biUnion
    (t := fun s => {y : Γ ⧸ X.K j | UpperTheory.Gal.G3.ind ℂ (X.K j) s y.out ≠ 0}) ?_).subset ?_
  · intro s hs
    exact hone s (Finset.mem_filter.1 hs).2
  · intro y hy
    obtain ⟨s, hs, a, b, e⟩ := hS y.out hy
    have hfs : f s ≠ 0 := by
      have h1 : f y.out = f s := by rw [e]; exact hb a b s
      rw [← h1]
      exact hy
    refine Set.mem_biUnion (Finset.mem_coe.2 (Finset.mem_filter.2 ⟨hs, hΔ s hfs⟩)) ?_
    show UpperTheory.Gal.G3.ind ℂ (X.K j) s y.out ≠ 0
    rw [UpperTheory.Gal.LocalSmoothExtension.FunctionDecomposition.ind_mem (K := X.K j)
      (DoubleCoset.mem_doubleCoset.2 ⟨(a : Γ), a.2, (b : Γ), b.2, e⟩)]
    exact one_ne_zero

open UpperTheory.Gal.LocalSmoothExtension in
theorem UpperTheory.Gal.LocalSmoothExtension.fnDecomp_of :
    FnDecomp := by
  intro B Γ _ X j f
  exact ⟨UpperTheory.Gal.LocalSmoothExtension.FunctionDecomposition.fwd X j f, UpperTheory.Gal.LocalSmoothExtension.FunctionDecomposition.bwd X j f⟩
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PGeoStep
section
set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField
open GlobalTheory.HodgeCoh
open UpperTheory.Gal.G3 (hodge ind)
open UpperTheory.Gal.Int.Geo (KS Lv Sc)
open scoped Classical

namespace UpperTheory.Gal.LocalSmoothExtension

theorem geoStep_of :
    HolomorphicLefschetzFormula → KSProj → FixK → LefSum → UpperTheory.Gal.G3.HodgeGood → UpperTheory.Gal.G3.HodgeTr → UpperTheory.Gal.G3.HopOp.{0} → UpperTheory.Gal.G3.OpTr.{0} → GeoStep := by
  intro W1 KSP FK LS HG HT HO OT p _ D G L sc gb std i₀ v hv k T N d hd h hΔ hreg α hα
  obtain ⟨m, hm1, -, hm3⟩ := T.X.deep (T.lev N) {(T.lev N, h)}
  obtain ⟨N₁, rfl⟩ := T.lev.surjective m
  obtain ⟨N', hdvd, hle⟩ : ∃ N' : Lv p, N.1 ∣ N'.1 ∧ T.X.K (T.lev N') ≤ T.X.K (T.lev N₁) := by
    refine ⟨⟨N.1 * N₁.1, le_trans N.2.1 (Nat.le_mul_of_pos_right _ (by have := N₁.2.1; omega)),
      Nat.coprime_mul_iff_left.2 ⟨N.2.2, N₁.2.2⟩⟩, Dvd.intro _ rfl, ?_⟩
    rw [T.K_eq, T.K_eq]
    exact UpperTheory.Gal.Int.Geo.KN_anti (Dvd.intro_left _ rfl)
  have a₀ : T.X.admitted (T.lev N') (T.lev N) 1 := T.X.isAdmissibleIntegralBasisChange_one (hle.trans hm1)
  have b₀ : T.X.admitted (T.lev N') (T.lev N) h := ⟨hΔ, fun u hu => hm3 (T.lev N, h) (by simp) u (hle hu)⟩
  obtain ⟨hcx, hfin, het, F, A, hF, hA, hsum⟩ := FK p D G L sc gb std i₀ v hv k T N' N hdvd d hd h a₀ b₀ hreg α hα
  refine ⟨hcx, fun y => ?_⟩
  haveI := T.X.fin (T.lev N') (T.lev N) a₀.1 a₀.2
  haveI := T.X.etale (T.lev N') (T.lev N) a₀.1 a₀.2
  haveI := hd
  have hq1 : T.X.tr _ _ 1 a₀.1 a₀.2 ≫ qAt T N = qAt T N' := T.X.tr_q _ _ _ _ _
  have hqh : T.X.tr _ _ h b₀.1 b₀.2 ≫ qAt T N = qAt T N' := T.X.tr_q _ _ _ _ _
  have hop := fun a b => HO T.X (hodge ℂ a b) (HG ℂ a b) (T.lev N') (T.lev N) h a₀ b₀
  have hW := W1 _ (qAt T N) d (KSP p D G L sc gb k T N).1 _ (qAt T N') (T.X.tr _ _ 1 a₀.1 a₀.2) (leg T N' N h b₀ α)
    hq1 (leg_q T N' N h b₀ α) hfin het F hF A hA
  have hne : (L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) ≠ 0 := by
    have := (hop 0 0).1
    rwa [T.K_eq N', T.K_eq N] at this
  have hc : (((L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) : ℕ) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 hne
  have key : ∀ a b, hk T N (ind ℂ (L.KN N.1) h⁻¹) a b ∘ₗ hodgePull (al_q T N α) a b =
      (((L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) : ℕ) : ℂ)⁻¹ •
        (hodgeTrace hq1 a b ∘ₗ hodgePull (leg_q T N' N h b₀ α) a b) := by
    intro a b
    have hIs := (hop a b).2
    rw [T.K_eq N', T.K_eq N] at hIs
    have e := (OT (hodge ℂ a b) (HG ℂ a b) (qAt T N) (qAt T N') (qAt T N) _ _ hq1 hqh (hodgeTrace hq1 a b)
      (HT ℂ a b _ _ _ hq1) _).1 hIs
    have e2 : hk T N (ind ℂ (L.KN N.1) h⁻¹) a b =
        (((L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) : ℕ) : ℂ)⁻¹ •
          (hodgeTrace hq1 a b ∘ₗ hodgePull hqh a b) := by
      have e' : (((L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) : ℕ) : ℂ) • hk T N (ind ℂ (L.KN N.1) h⁻¹) a b =
          hodgeTrace hq1 a b ∘ₗ hodgePull hqh a b := e
      rw [← e', smul_smul, inv_mul_cancel₀ hc, one_smul]
    rw [e2]
    ext x
    simp only [LinearMap.comp_apply, LinearMap.smul_apply]
    rw [hodgePull_comp (al_q T N α) hqh (leg_q T N' N h b₀ α) a b x]
    rfl
  have hinner : ∀ a, ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b * LinearMap.trace ℂ _
        (hk T N (ind ℂ (L.KN N.1) h⁻¹) a b ∘ₗ hodgePull (al_q T N α) a b) =
      (((L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) : ℕ) : ℂ)⁻¹ *
        ∑ x ∈ F, (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A x).map Polynomial.C)).coeff a / (1 - A x).det := by
    intro a
    rw [← (hW a).2, Finset.mul_sum]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [key a b, map_smul, smul_eq_mul]
    ring
  have hfinal : altTr (qAt T N) d (fun a b => hk T N (ind ℂ (L.KN N.1) h⁻¹) a b ∘ₗ hodgePull (al_q T N α) a b) y =
      (((L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) : ℕ) : ℂ)⁻¹ * ∑ x ∈ F, UpperTheory.Gal.W2.lefTerm (A x) y := by
    unfold altTr
    calc _ = ∑ a ∈ Finset.range (d + 1), (-y) ^ a *
            ((((L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) : ℕ) : ℂ)⁻¹ *
              ∑ x ∈ F, (Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A x).map Polynomial.C)).coeff a / (1 - A x).det) :=
          Finset.sum_congr rfl fun a _ => by rw [hinner a]
      _ = (((L.KN N'.1).relIndex (UpperTheory.Gal.G3.lev (L.KN N.1) h) : ℕ) : ℂ)⁻¹ * ∑ x ∈ F, ∑ a ∈ Finset.range (d + 1), (-y) ^ a *
            ((Matrix.det (1 + (Polynomial.X : Polynomial ℂ) • (A x).map Polynomial.C)).coeff a / (1 - A x).det) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun a _ => by ring
      _ = _ := by
          congr 1
          exact Finset.sum_congr rfl fun x _ => LS d (A x) y
  rw [hfinal, hsum y, ← mul_assoc, inv_mul_cancel₀ hc, one_mul]

end UpperTheory.Gal.LocalSmoothExtension
end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHodgeEig
section
open UpperTheory.Gal.LocalSmoothExtension

open GlobalTheory.HodgeCoh UpperTheory.Gal.CertificateRingHomMap in
theorem UpperTheory.Gal.LocalSmoothExtension.hodgeEig_of :
    HodgeTr → KSProj → HodgeFin → UnifBound → HExpInj → CoeffOcc → EigOf → HopWord → UpperTheory.Gal.G3.HodgeGood → HodgeEig := by
  intro hTr hProj hFin hUnif hInj hCo hEig hWord hGood
  intro p _ D G L hSc lam hlam
  classical
  let κ : ((D.F →+* ℂ) → Fin G.n → ℕ) → Fin D.a → (Fin G.n → ℕ) → ℕ := fun lam' i₀ h =>
    if H : IsHExp (D.tau i₀) (epsOf D) lam' h then (hTr p D G L lam' i₀ h H).choose else 0
  obtain ⟨k, hkB⟩ := hUnif D.F G.n (Fin D.a) D.tau (epsOf D) lam κ
  refine ⟨k, ?_⟩
  intro gb hgb T N σ i₀ h hH J ψ θ f hψ hf hS i
  have hκ : (hTr p D G L (conjWt σ lam) i₀ h hH).choose ≤ k := by
    have := hkB σ i₀ h hH
    simpa only [κ, dif_pos hH] using this
  obtain ⟨c, hc⟩ := (hTr p D G L (conjWt σ lam) i₀ h hH).choose_spec k hκ
  obtain ⟨hproj, d, hd⟩ := hProj p D G L hSc gb k T N
  have hcT := hc hSc gb hgb T N d hd
  have hG : ∀ a b, (UpperTheory.Gal.G3.hodge ℂ a b).Good := fun a b => hGood ℂ a b
  haveI hFD : ∀ b : Fin (d + 1), FiniteDimensional ℂ (hodgeH (qAt T N) (h i) b.1) :=
    fun b => hFin _ _ d hd hproj _ _
  have hWd : ∀ (a b : ℕ) (w : List J), T.X.IsFn (T.lev N) (wordFn (L.KN N.1) ψ w f) ∧
      hk T N (wordFn (L.KN N.1) ψ w f) a b = (w.map fun j => hk T N (ψ j) a b).prod * hk T N f a b := by
    intro a b w
    have := ((hWord _ _ T.X (UpperTheory.Gal.G3.hodge ℂ a b) (hG a b) (T.lev N)).2 J ψ f hψ hf).1 w
    rw [T.K_eq] at this
    exact this
  have hPoly : ∀ (a b : ℕ) (s : List J →₀ ℂ), T.X.IsFn (T.lev N) (polyFn (L.KN N.1) ψ s f) ∧
      hk T N (polyFn (L.KN N.1) ψ s f) a b = wop (fun j => hk T N (ψ j) a b) s * hk T N f a b := by
    intro a b s
    have := ((hWord _ _ T.X (UpperTheory.Gal.G3.hodge ℂ a b) (hG a b) (T.lev N)).2 J ψ f hψ hf).2 s
    rw [T.K_eq] at this
    exact this
  obtain ⟨hcomm, V, _, _, _, ξ, hξ, hspec⟩ := hS
  have hcm : ∀ (b : Fin (d + 1)) (j j' : J) (w : List J),
      hk T N (ψ j) (h i) b.1 * hk T N (ψ j') (h i) b.1 * (w.map fun j => hk T N (ψ j) (h i) b.1).prod *
          hk T N f (h i) b.1 =
        hk T N (ψ j') (h i) b.1 * hk T N (ψ j) (h i) b.1 * (w.map fun j => hk T N (ψ j) (h i) b.1).prod *
          hk T N f (h i) b.1 := by
    intro b j j' w
    have h1 := (hWd (h i) b.1 (j :: j' :: w)).2
    have h2 := (hWd (h i) b.1 (j' :: j :: w)).2
    rw [hcomm j j' w, h2] at h1
    simpa only [List.map_cons, List.prod_cons, mul_assoc] using h1.symm
  obtain ⟨s, hs1, hs⟩ := hEig (Fin (d + 1)) J (fun b => hodgeH (qAt T N) (h i) b.1)
    (fun b j => hk T N (ψ j) (h i) b.1) (fun b => hk T N f (h i) b.1) θ hcm
  have hne : wop θ s ≠ 0 := by rw [hs1]; exact one_ne_zero
  obtain ⟨a, hgoodF, hdT⟩ := hspec s hne
  have hFfn := (hPoly 0 0 (wmul a s)).1
  have hy := fun y => hcT V ξ hξ _ hFfn hgoodF y
  have hocc := hCo d G.n
    (fun a' => ∑ b ∈ Finset.range (d + 1), (-1 : ℂ) ^ b *
      LinearMap.trace ℂ _ (hk T N (polyFn (L.KN N.1) ψ (wmul a s) f) a' b ∘ₗ cutD T N c a' b)) _ h
    (hInj D.F G.n (D.tau i₀) (epsOf D) (conjWt σ lam) h (fun τ => hlam _) hH) hdT hy i
  obtain ⟨b, hb, hb0⟩ := Finset.exists_ne_zero_of_sum_ne_zero hocc
  have hne0 : hk T N (polyFn (L.KN N.1) ψ (wmul a s) f) (h i) b ≠ 0 := by
    intro e
    apply hb0
    rw [e, LinearMap.zero_comp, map_zero, mul_zero]
  rw [(hPoly _ _ _).2, wop_wmul, mul_assoc] at hne0
  have hu : wop (fun j => hk T N (ψ j) (h i) b) s * hk T N f (h i) b ≠ 0 :=
    fun e => hne0 (by rw [e, mul_zero])
  obtain ⟨x, hx0, hx⟩ := hs ⟨b, Finset.mem_range.1 hb⟩ hu
  exact ⟨b, x, hx0, hx⟩
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHodgeFin
section
open UpperTheory.Gal.LocalSmoothExtension

open AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.HodgeCoh

theorem UpperTheory.Gal.LocalSmoothExtension.hodgeFin_of :
    HolomorphicLefschetzFormula → HodgeFin := by
  intro hW Z s d hsm hproj a b
  haveI := hsm
  have hF : ∀ y : CxPts (Scheme.emptyTo Z ≫ s) (RingHom.id ℂ),
      y ∈ (∅ : Finset (CxPts (Scheme.emptyTo Z ≫ s) (RingHom.id ℂ))) ↔
        y.1 ≫ Scheme.emptyTo Z = y.1 ≫ Scheme.emptyTo Z :=
    fun y => (isEmptyElim (y.1.base (Classical.arbitrary _)) : False).elim
  have key := hW Z s d hproj ∅ (Scheme.emptyTo Z ≫ s) (Scheme.emptyTo Z) (Scheme.emptyTo Z) rfl rfl
    inferInstance inferInstance ∅ hF (fun _ => 0) (fun y hy => by simp at hy) a
  exact key.1 b
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PHodgeTr
section
set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits NumberField
open GlobalTheory.HodgeCoh GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCx GlobalTheory.LKDef GlobalTheory.RootSumWeights GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open UpperTheory.Gal.Int.Geo (KS Lv Sc)
open UpperTheory.Gal.G3 (hodge ind)
open UpperTheory.Gal.LocalSmoothExtension

theorem UpperTheory.Gal.LocalSmoothExtension.hodgeTr_of :
    GroupTop → FnDecomp → HopWord → AltLin → GeoStep → CxLin → UpperTheory.Gal.G3.HodgeGood → HodgeTr := by
  classical
  intro hTop hFD hHW hAL hGS hCL hHG p _ D G L lam i₀ h hh
  obtain ⟨k₀, hk'⟩ := hTop p D G L lam i₀ h hh
  refine ⟨k₀, fun k hkk => ?_⟩
  obtain ⟨c, hc1, hc2⟩ := hk' k hkk
  refine ⟨c, fun hSc gb hStd T N d hsm V _ _ _ ξ hξ f hfn hG y => ?_⟩
  have hcard : 0 < Fintype.card {v : InfinitePlace G.F // sigPosH (G.gram_herm v) = 1} := by
    change 0 < G.a
    exact hSc.ga.symm ▸ Nat.zero_lt_one
  obtain ⟨⟨v, hv⟩⟩ := Fintype.card_pos_iff.1 hcard
  obtain ⟨Lv, hLv⟩ := GlobalTheory.LKGeo.KNLevel.exists_level_eq_KN p D G L N.1 (by have := N.2.1; omega)
  have hK := T.K_eq N
  obtain ⟨hHecke, m, g, cc, hΔ, hdec, hsupp⟩ := (hFD _ _ T.X (T.lev N) f).1 hfn
  rw [hK] at hHecke hdec hsupp
  have hreg : ∀ i x, ind ℂ (L.KN N.1) (g i)⁻¹ x ≠ 0 → RegAf G x := fun i x hx => hG.reg x (hsupp i x hx)
  have hfnu : ∀ i, T.X.IsFn (T.lev N) (ind ℂ (L.KN N.1) (g i)⁻¹) := fun i => by
    have e := (UpperTheory.Gal.G3.pFnRing T.X ℂ (T.lev N)).1 _ (hΔ i)
    rwa [hK] at e
  have hgeo := fun i α hα => hGS p D G L hSc gb hStd i₀ v hv k T N d hsm (g i) (hΔ i) (hreg i) α hα
  have hfin : ∀ i, CxFin G v (L.KN N.1) (ind ℂ (L.KN N.1) (g i)⁻¹) := fun i =>
    (hgeo i (fun _ => 2) (fun _ => ⟨two_ne_zero, dvd_rfl⟩)).1
  have hhk : ∀ a b, hk T N f a b = ∑ i, cc i • hk T N (ind ℂ (L.KN N.1) (g i)⁻¹) a b := fun a b => by
    have e := ((hHW _ _ T.X (hodge ℂ a b) (hHG ℂ a b) (T.lev N)).1 m _ cc hfnu).2
    rw [← hdec] at e
    exact e
  have e1 : altTr (qAt T N) d (fun a b => hk T N f a b ∘ₗ cutD T N c a b) y =
      ∑ i, cc i * c.sum fun α r => r * cxTotalM G v (cW L i₀ v α y) (L.KN N.1) (ind ℂ (L.KN N.1) (g i)⁻¹) (Kp G) (oneP G) := by
    have e := hAL _ (qAt T N) d m (Fin k → 𝓞 D.F) (fun i a b => hk T N (ind ℂ (L.KN N.1) (g i)⁻¹) a b) cc c
      (fun α a b => hodgePull (al_q T N α) a b) y
    simp only [hhk, cutD]
    rw [e]
    refine Finset.sum_congr rfl fun i _ => congrArg (cc i * ·) (Finsupp.sum_congr fun α hα => ?_)
    rw [(hgeo i α (hc1 α hα)).2 y]
  have e2 := hCL p G v (L.KN N.1) m _ cc hfin (Fin k → 𝓞 D.F) c (fun α => cW L i₀ v α y)
  rw [← hdec] at e2
  have e3 := hc2 hSc.a1 hSc.ga hSc.odd v hv V ξ hξ Lv f
  rw [hLv] at e3
  rw [e1, ← e2]
  exact e3 hHecke hG y
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LefschetzSigmaSums.PKSProj
section
open AlgebraicGeometry CategoryTheory Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen
open UpperTheory.Gal.LocalSmoothExtension
open UpperTheory.Gal.Int.Geo (KS Lv Sc)

theorem UpperTheory.Gal.LocalSmoothExtension.kSProj_of :
    ZSm → ZPr → KSProj := by
  intro hSm hPr p _ D G L hSc gb k T N
  have hq : qAt T N = (T.e N).hom ≫ ((KS.pow (T.M N).univ.A k).hom ≫ (T.M N).s) := (T.e_q N).symm
  rw [hq]
  constructor
  · obtain ⟨M, i, hi, hi'⟩ := hPr p D hSc.cpt gb N.1 N.2.1 N.2.2 (T.M N) k
    refine ⟨M, (T.e N).hom ≫ i, ?_, ?_⟩
    · haveI := hi
      infer_instance
    · rw [Category.assoc, hi']
  · obtain ⟨d, hd⟩ := hSm D.toG gb N.1 N.2.1 (T.M N) k
    haveI := hd
    have h0 : SmoothOfRelativeDimension 0 (T.e N).hom := inferInstance
    have h2 := AlgebraicGeometry.smoothOfRelativeDimension_comp (n := 0) (m := d) (T.e N).hom
      ((KS.pow (T.M N).univ.A k).hom ≫ (T.M N).s)
    rw [zero_add] at h2
    exact ⟨d, h2⟩
end

