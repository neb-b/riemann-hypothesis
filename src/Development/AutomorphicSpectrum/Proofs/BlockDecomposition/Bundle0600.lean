module

public import Mathlib
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.SquareIntegrableTempered.CentredSegments.IrreducibleUnif
public import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.Bundle0002
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorJacquetEigenLeft
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeOperatorJacquetEigenRight
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0583
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0356
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.DifferentialFormsCech.AffineHodgeIsomorphisms.IsFormT
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.CosieveBot
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.Bundle0003
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.HodgeSurjectivity.RelativeLiftCosieves.ZarAbs
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.Imports
public import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.GrCechFin
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.StCocycle
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OntoFormLaws
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0466
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0589
public import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilSiegelTheta.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd
public import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsCellOfIsSubquotient
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0285
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0289
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0379
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0284
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0328

@[expose] public section

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HeckeSpectralOfStrictExponent
section
open Filter Topology MeasureTheory GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult ValuativeRel

namespace GlobalTheory.CompanionTheory.HeckeBound

theorem norm_lt_of_norm_mul_cpow_lt (q e : ℕ) (hq : 0 < q) (μ : ℂ)
    (h : ‖μ * (q : ℂ) ^ ((e : ℂ) / 2)‖ < 1) : ‖μ‖ < (q : ℝ) ^ (-((e : ℝ) / 2)) := by
  have hq' : (0 : ℝ) < q := by exact_mod_cast hq
  have hre : (((e : ℂ) / 2)).re = (e : ℝ) / 2 := by
    have : ((e : ℂ) / 2) = (((e : ℝ) / 2 : ℝ) : ℂ) := by push_cast; ring
    rw [this, Complex.ofReal_re]
  rw [norm_mul, Complex.norm_natCast_cpow_of_pos hq, hre] at h
  have hp : 0 < (q : ℝ) ^ ((e : ℝ) / 2) := Real.rpow_pos_of_pos hq' _
  rw [Real.rpow_neg hq'.le, ← one_div, lt_div_iff₀ hp]
  exact h

theorem heckeSpectral_of_maxExpStrict (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (N : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V]
    (π : Representation ℂ (GL (Fin N) k) V) (hs : IsSmooth π) (hi : π.IsIrreducible)
    (hA : GlobalTheory.Published.IrreducibleAdmissibleGL) (hF : GlobalTheory.Published.StandardFunctorsFiniteLength)
    (hM : Zls.MaxExpStrict π) : Zls.HeckeSpectral π := by
  intro m hm j hj hjN T hT μ hμ
  have hq : 0 < Nat.card 𝓀[k] := Nat.card_pos
  by_cases hμ0 : μ = 0
  · subst hμ0
    simpa using Real.rpow_pos_of_pos (by exact_mod_cast hq : (0 : ℝ) < (Nat.card 𝓀[k] : ℝ)) _
  obtain ⟨w, hw⟩ := hμ.exists_hasEigenvector
  let d : Fin 2 → ℕ := ![j, N - j]
  have hd : ∑ a, d a = N := by
    simp only [d, Fin.sum_univ_two, Matrix.cons_val_zero, Matrix.cons_val_one]
    omega
  have d0 : d 0 = j := rfl
  have d1 : d 1 = N - j := rfl
  have hd0 : 0 < d 0 := hj
  have hd1 : 0 < d 1 := by rw [d1]; omega
  have hT' : Zls.IsHeckeOp π m (Zls.diagPow k N (Zls.omegaVec N (d 0))) T := hT
  have hTw : T w = μ • w := hw.apply_eq_smul
  have hmk : (Submodule.Quotient.mk (w : V) : Jacquet π (unipRad k (stdBlocks d hd))) ≠ 0 := by
    intro h0
    obtain ⟨r, hr⟩ := _root_.GlobalTheory.CompanionTheory.HeckeNilp.hecke_nilpotent k N V π hs m hm d hd hd0 hd1 T hT' w h0
    rw [hw.pow_apply r] at hr
    exact (smul_ne_zero (pow_ne_zero r hμ0) hw.2) hr
  have hjac := _root_.GlobalTheory.CompanionTheory.HeckeJacquet.hecke_omega_jacquet k N V π hs m hm d hd hd0 hd1 T hT' w
  have heig : (Submodule.Quotient.mk (π (Zls.diagPow k N (Zls.omegaVec N (d 0))) (w : V)) :
      Jacquet π (unipRad k (stdBlocks d hd))) =
      μ • (Submodule.Quotient.mk (w : V) : Jacquet π (unipRad k (stdBlocks d hd))) := by
    rw [← hjac, hTw]
    rfl
  obtain ⟨x, hx, hxd, hjm, hs0, c1, hs1⟩ :=
    GlobalTheory.T.jacquet_quotient_eigenvector k N V π hs hi hA hF d hd hd0 hd1 μ w hmk heig
  have hpos : ∀ a, 0 < (x a).1 := by
    intro a
    rw [hxd a]
    fin_cases a
    · exact hd0
    · exact hd1
  have hE := hM x hx hpos hjm
  have hc := (hE (Zls.unifU k) (_root_.GlobalTheory.CompanionTheory.UnifPow.tendsto_unifU_pow k)
    ![μ * (Nat.card 𝓀[k] : ℂ) ^ (((d 0 * d 1 : ℕ) : ℂ) / 2), c1]
    (by
      intro i
      fin_cases i
      · exact hs0
      · exact hs1)).1 0 (by simp)
  have hfil : Finset.univ.filter (· ≤ (0 : Fin 2)) = {0} := by decide
  rw [hfil, Finset.prod_singleton] at hc
  have := norm_lt_of_norm_mul_cpow_lt (Nat.card 𝓀[k]) (d 0 * d 1) hq μ hc
  simpa [d0, d1] using this

end GlobalTheory.CompanionTheory.HeckeBound
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormCupWedge
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

noncomputable section
namespace GlobalTheory.CompanionTheory.OmCup
open CrystallineSemistableComparison CrystallineSemistableComparison.Pb CrystallineSemistableComparison.HT CrystallineSemistableComparison.Om.L2

variable {K : Type} [CommRing K] {X : Scheme.{0}} {q : X ⟶ Spec (CommRingCat.of K)}

theorem mk_carry (Λ : LiftsT q) {T T' : Thick (smFun X q)} (φ : T ⟶ T') (g : Γ(X, ⊤)) :
    Ideal.Quotient.mk T'.J (φ.φ (Λ.v T g)) = Ideal.Quotient.mk T'.J (Λ.v T' g) := by
  rw [Λ.hv T' g]
  refine Eq.trans ?_ (GlobalTheory.CompanionTheory.GrForm.ev_nat (q := q) φ (inTop q T) (inTop q T') g).symm
  rw [← Λ.hv T g]
  rfl

def up (Λ : LiftsT q) {n : ℕ} (s : ComposableArrows (Thick (smFun X q)) n) (i : Fin (n + 1)) (g : Γ(X, ⊤)) :
    (s.obj (Fin.last n)).B :=
  (s.map (homOfLE (Fin.le_last i))).φ (Λ.v _ g)

theorem mk_up (Λ : LiftsT q) {n : ℕ} (s : ComposableArrows (Thick (smFun X q)) n) (i : Fin (n + 1)) (g : Γ(X, ⊤)) :
    Ideal.Quotient.mk (s.obj (Fin.last n)).J (up Λ s i g) = Ideal.Quotient.mk _ (Λ.v (s.obj (Fin.last n)) g) :=
  mk_carry Λ _ g

theorem carry (Λ : LiftsT q) {m n : ℕ} (s : ComposableArrows (Thick (smFun X q)) n) (p : Fin (m + 1) → Fin (n + 1))
    (hp : Monotone p) (k : Fin (m + 1)) (g : Γ(X, ⊤)) :
    (s.map (homOfLE (Fin.le_last (p (Fin.last m))))).φ (up Λ (hp.functor ⋙ s) k g) = up Λ s (p k) g := by
  have e : (hp.functor ⋙ s).map (homOfLE (Fin.le_last k)) ≫ s.map (homOfLE (Fin.le_last (p (Fin.last m)))) =
      s.map (homOfLE (Fin.le_last (p k))) := by
    change s.map _ ≫ s.map _ = _
    rw [← s.map_comp]
    exact congrArg s.map (Subsingleton.elim _ _)
  exact congrArg (fun ψ : (s.obj (p k)) ⟶ (s.obj (Fin.last n)) => ψ.φ (Λ.v _ g)) e

theorem form_eq (Λ : LiftsT q) {a : ℕ} (g₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤)) (s : ComposableArrows (Thick (smFun X q)) a) :
    Λ.form g₀ g s = Λ.v _ g₀ * ∏ k : Fin a, (up Λ s k.succ (g k) - up Λ s k.castSucc (g k)) := rfl

theorem prod_mem (Λ : LiftsT q) {a : ℕ} (g : Fin a → Γ(X, ⊤)) (s : ComposableArrows (Thick (smFun X q)) a) :
    ∏ k : Fin a, (up Λ s k.succ (g k) - up Λ s k.castSucc (g k)) ∈ pdP (s.obj (Fin.last a)).δ a := by
  have key : ∀ (S : Finset (Fin a)), ∏ k ∈ S, (up Λ s k.succ (g k) - up Λ s k.castSucc (g k)) ∈
      pdP (s.obj (Fin.last a)).δ S.card := by
    classical
    intro S
    induction S using Finset.induction_on with
    | empty =>
      rw [Finset.prod_empty]
      exact Ideal.subset_span ⟨[], by simp, by simp, by simp⟩
    | insert c S hc ih =>
      rw [Finset.prod_insert hc, Finset.card_insert_of_notMem hc, Nat.add_comm S.card 1]
      refine dividedPowerFiltration_mul _ 1 S.card ?_ ih
      refine (s.obj (Fin.last a)).J_le_pdPow_one ?_
      rw [← Ideal.Quotient.eq, mk_up, mk_up]
  simpa using key Finset.univ

theorem form_mem (Λ : LiftsT q) {a : ℕ} (g₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤)) (s : ComposableArrows (Thick (smFun X q)) a) :
    Λ.form g₀ g s ∈ pdP (s.obj (Fin.last a)).δ a :=
  Ideal.mul_mem_left _ _ (prod_mem Λ g s)

theorem carry_form (Λ : LiftsT q) {m n : ℕ} (s : ComposableArrows (Thick (smFun X q)) n) (p : Fin (m + 1) → Fin (n + 1))
    (hp : Monotone p) (g₀ : Γ(X, ⊤)) (g : Fin m → Γ(X, ⊤)) :
    (s.map (homOfLE (Fin.le_last (p (Fin.last m))))).φ (Λ.form g₀ g (hp.functor ⋙ s)) =
      up Λ s (p (Fin.last m)) g₀ * ∏ k : Fin m, (up Λ s (p k.succ) (g k) - up Λ s (p k.castSucc) (g k)) := by
  rw [form_eq, map_mul, map_prod]
  refine congrArg₂ (· * ·) rfl (Finset.prod_congr rfl fun k _ => ?_)
  rw [map_sub, carry, carry]

def someLifts (q : X ⟶ Spec (CommRingCat.of K)) : LiftsT q where
  v T g := Function.surjInv Ideal.Quotient.mk_surjective
    (ev (γ := dividedPowersBot K) (p := 0) (q := q) (κ := Ideal.Quotient.mk ⊥) T (inTop q T) g)
  hv T g := Function.surjInv_eq _ _

theorem isFormT_unique {a : ℕ} {g₀ : Γ(X, ⊤)} {g : Fin a → Γ(X, ⊤)} {c c' : Hdg q a a}
    (h : IsFormT q g₀ g c) (h' : IsFormT q g₀ g c') : c = c' := by
  obtain ⟨f, hf, e, hz⟩ := h (someLifts q)
  obtain ⟨f', hf', e', hz'⟩ := h' (someLifts q)
  have : f = f' := funext fun s => Subtype.ext ((hz s).trans (hz' s).symm)
  subst this
  exact e.trans e'.symm

theorem alg {B : Type} [CommRing B] (x₁ x₂ v p₁ p₂ : B) :
    (x₁ * x₂ - v) * (p₁ * p₂) = x₁ * p₁ * (x₂ * p₂) - v * (p₁ * p₂) := by ring

theorem cup_rep (Λ : LiftsT q) {a b : ℕ} (g₀ h₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤)) (h : Fin b → Γ(X, ⊤))
    (f : CH.Cn (grT (smFun X q) a) a) (f' : CH.Cn (grT (smFun X q) b) b)
    (hf : ∀ s, (show sqM _ _ _ from f s).1 = Ideal.Quotient.mk _ (Λ.form g₀ g s))
    (hf' : ∀ s, (show sqM _ _ _ from f' s).1 = Ideal.Quotient.mk _ (Λ.form h₀ h s))
    (s : ComposableArrows (Thick (smFun X q)) (a + b)) :
    (show sqM _ _ _ from (grOk (smFun X q) (rfl : a + b = a + b)).pair.cupC (rfl : a + b = a + b) f f' s).1 =
      Ideal.Quotient.mk _ (Λ.form (g₀ * h₀) (Fin.append g h) s) := by
  have hm := CH.front_mono (rfl : a + b = a + b)
  have hb := CH.back_mono (rfl : a + b = a + b)
  have e1 : f (hm.functor ⋙ s) = sqMk (thFil (smFun X q) (a : ℤ)) (thFil (smFun X q) ((a : ℤ) + 1)) (Λ.form g₀ g (hm.functor ⋙ s))
      (form_mem Λ g₀ g _) := Subtype.ext (hf _)
  have e2 : f' (hb.functor ⋙ s) = sqMk (thFil (smFun X q) (b : ℤ)) (thFil (smFun X q) ((b : ℤ) + 1)) (Λ.form h₀ h (hb.functor ⋙ s))
      (form_mem Λ h₀ h _) := Subtype.ext (hf' _)
  have hM := grOk (smFun X q) (rfl : a + b = a + b)
  have t1 : CH.term (grT (smFun X q) a) s f (CH.front (rfl : a + b = a + b)) hm =
      sqMk (thFil (smFun X q) (a : ℤ)) (thFil (smFun X q) ((a : ℤ) + 1))
        ((s.map (homOfLE (Fin.le_last (CH.front (rfl : a + b = a + b) (Fin.last a))))).φ (Λ.form g₀ g (hm.functor ⋙ s)))
        ((thFil (smFun X q) (a : ℤ)).map_mem _ (show _ ∈ (thFil (smFun X q) (a : ℤ)).S _ from form_mem Λ g₀ g (hm.functor ⋙ s))) := by
    unfold CH.term
    rw [e1]
    rfl
  have t2 : CH.term (grT (smFun X q) b) s f' (CH.back (rfl : a + b = a + b)) hb =
      sqMk (thFil (smFun X q) (b : ℤ)) (thFil (smFun X q) ((b : ℤ) + 1))
        ((s.map (homOfLE (Fin.le_last (CH.back (rfl : a + b = a + b) (Fin.last b))))).φ (Λ.form h₀ h (hb.functor ⋙ s)))
        ((thFil (smFun X q) (b : ℤ)).map_mem _ (show _ ∈ (thFil (smFun X q) (b : ℤ)).S _ from form_mem Λ h₀ h (hb.functor ⋙ s))) := by
    unfold CH.term
    rw [e2]
    rfl
  have c : (grOk (smFun X q) (rfl : a + b = a + b)).pair.cupC (rfl : a + b = a + b) f f' s =
      (grOk (smFun X q) (rfl : a + b = a + b)).mul (CH.term (grT (smFun X q) a) s f (CH.front (rfl : a + b = a + b)) hm)
        (CH.term (grT (smFun X q) b) s f' (CH.back (rfl : a + b = a + b)) hb) := rfl
  rw [c, t1, t2, MulOk.mul_mk]
  change Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
  rw [carry_form Λ s _ hm g₀ g, carry_form Λ s _ hb h₀ h, form_eq]
  have hprod : ∏ k : Fin (a + b), (up Λ s k.succ (Fin.append g h k) - up Λ s k.castSucc (Fin.append g h k)) =
      (∏ k : Fin a, (up Λ s (CH.front (rfl : a + b = a + b) k.succ) (g k) - up Λ s (CH.front (rfl : a + b = a + b) k.castSucc) (g k))) *
      ∏ k : Fin b, (up Λ s (CH.back (rfl : a + b = a + b) k.succ) (h k) - up Λ s (CH.back (rfl : a + b = a + b) k.castSucc) (h k)) := by
    rw [Fin.prod_univ_add]
    refine congrArg₂ (· * ·) (Finset.prod_congr rfl fun i _ => ?_) (Finset.prod_congr rfl fun i _ => ?_)
    · rw [Fin.append_left]
      rfl
    · rw [Fin.append_right]
      have e3 : (Fin.natAdd a i).succ = CH.back (rfl : a + b = a + b) i.succ := Fin.ext (by simp [CH.back]; omega)
      have e4 : (Fin.natAdd a i).castSucc = CH.back (rfl : a + b = a + b) i.castSucc := Fin.ext (by simp [CH.back])
      rw [e3, e4]
  have hP := prod_mem Λ (Fin.append g h) s
  rw [hprod] at hP ⊢
  rw [Ideal.Quotient.eq]
  generalize (∏ k : Fin a, (up Λ s (CH.front (rfl : a + b = a + b) k.succ) (g k) - up Λ s (CH.front (rfl : a + b = a + b) k.castSucc) (g k))) = P₁ at hP ⊢
  generalize (∏ k : Fin b, (up Λ s (CH.back (rfl : a + b = a + b) k.succ) (h k) - up Λ s (CH.back (rfl : a + b = a + b) k.castSucc) (h k))) = P₂ at hP ⊢
  have hJ : up Λ s (CH.front (rfl : a + b = a + b) (Fin.last a)) g₀ * up Λ s (CH.back (rfl : a + b = a + b) (Fin.last b)) h₀ -
      Λ.v _ (g₀ * h₀) ∈ (s.obj (Fin.last (a + b))).J := by
    rw [← Ideal.Quotient.eq, map_mul, mk_up, mk_up, Λ.hv, Λ.hv, Λ.hv, map_mul]
  have hm2 := dividedPowerFiltration_mul _ 1 (a + b) ((s.obj (Fin.last (a + b))).J_le_pdPow_one hJ) hP
  have e5 : (((a + b : ℕ) : ℤ) + 1).toNat = 1 + (a + b) := by omega
  change _ ∈ pdP _ (((a + b : ℕ) : ℤ) + 1).toNat
  rw [e5]
  rw [alg] at hm2
  exact hm2

theorem isFormT_cup {a b : ℕ} {g₀ h₀ : Γ(X, ⊤)} {g : Fin a → Γ(X, ⊤)} {h : Fin b → Γ(X, ⊤)} {x : Hdg q a a} {y : Hdg q b b}
    (hx : IsFormT q g₀ g x) (hy : IsFormT q h₀ h y) :
    IsFormT q (g₀ * h₀) (Fin.append g h) (cupH q rfl rfl x y) := by
  intro Λ
  obtain ⟨f, hf, ex, hz⟩ := hx Λ
  obtain ⟨f', hf', ey, hz'⟩ := hy Λ
  obtain ⟨hc, e⟩ := CrystallineSemistableComparison.P.cup_cls (grOk (smFun X q) (rfl : a + b = a + b)).pair (rfl : a + b = a + b) f f' hf hf'
  refine ⟨_, hc, ?_, cup_rep Λ g₀ h₀ g h f f' hz hz'⟩
  exact (congrArg₂ (fun u v => (grOk (smFun X q) (rfl : a + b = a + b)).pair.cup (rfl : a + b = a + b) u v) ex ey).trans e

theorem wedge_form {A : Type} [CommRing A] [Algebra K A] {a b : ℕ} (g₀ h₀ : A) (g : Fin a → A) (h : Fin b → A) :
    wedgeOm K A (rfl : a + b = a + b) (CrystallineSemistableComparison.Onto.form K g₀ g) (CrystallineSemistableComparison.Onto.form K h₀ h) =
      CrystallineSemistableComparison.Onto.form K (g₀ * h₀) (Fin.append g h) := by
  refine Subtype.ext ?_
  rw [coe_wedgeOm]
  simp only [CrystallineSemistableComparison.Onto.form, Submodule.coe_smul, exteriorPower.ιMulti_apply_coe]
  rw [smul_mul_smul_comm, ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, ExteriorAlgebra.ιMulti_apply, ← List.prod_append,
    ← List.ofFn_fin_append]
  refine congrArg (fun v => (g₀ * h₀) • (List.ofFn v).prod) (funext fun i => ?_)
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i <;> simp

theorem bilin_ext {H₁ H₂ H₃ M₁ M₂ M₃ : Type*} [AddCommGroup H₁] [AddCommGroup H₂] [AddCommGroup H₃] [AddCommGroup M₁]
    [AddCommGroup M₂] [AddCommGroup M₃] [Module K H₁] [Module K H₂] [Module K H₃] [Module K M₁] [Module K M₂] [Module K M₃]
    (e₁ : H₁ ≃ₗ[K] M₁) (e₂ : H₂ ≃ₗ[K] M₂) (e₃ : H₃ ≃ₗ[K] M₃) (B : H₁ →ₗ[K] H₂ →ₗ[K] H₃) (Wd : M₁ →ₗ[K] M₂ →ₗ[K] M₃)
    (S₁ : Set M₁) (S₂ : Set M₂) (h₁ : Submodule.span K S₁ = ⊤) (h₂ : Submodule.span K S₂ = ⊤)
    (gen : ∀ ω ∈ S₁, ∀ η ∈ S₂, e₃ (B (e₁.symm ω) (e₂.symm η)) = Wd ω η) (x : H₁) (y : H₂) :
    e₃ (B x y) = Wd (e₁ x) (e₂ y) := by
  have all : ∀ (ω : M₁) (η : M₂), e₃ (B (e₁.symm ω) (e₂.symm η)) = Wd ω η := by
    intro ω η
    have hω : ω ∈ Submodule.span K S₁ := h₁ ▸ Submodule.mem_top
    have hη : η ∈ Submodule.span K S₂ := h₂ ▸ Submodule.mem_top
    induction hω using Submodule.span_induction with
    | zero => simp
    | add u v _ _ hu hv => simp only [map_add (f := _), LinearMap.add_apply, hu, hv]
    | smul r u _ hu => simp only [map_smul, LinearMap.smul_apply, hu]
    | mem u hu =>
      induction hη using Submodule.span_induction with
      | zero => simp
      | add u v _ _ hu hv => simp only [map_add (f := _), hu, hv]
      | smul r u _ hu => simp only [map_smul, hu]
      | mem v hv => exact gen u hu v hv
  simpa using all (e₁ x) (e₂ y)

theorem exists_bil (q : X ⟶ Spec (CommRingCat.of K)) (a b : ℕ) :
    ∃ B : Hdg q a a →ₗ[K] Hdg q b b →ₗ[K] Hdg q (a + b) (a + b), ∀ u v, B u v = cupH q rfl rfl u v := by
  obtain ⟨bil, hbil⟩ := CrystallineSemistableComparison.P.cup_bilin (grOk (smFun X q) (rfl : a + b = a + b)).pair (rfl : a + b = a + b)
  exact ⟨bil, hbil⟩

theorem gen_eq {a b : ℕ} (eA : Hdg q a a ≃ₗ[K] OmU q ⊤ a) (eB : Hdg q b b ≃ₗ[K] OmU q ⊤ b)
    (eC : Hdg q (a + b) (a + b) ≃ₗ[K] OmU q ⊤ (a + b)) (hA : IsOmT q a eA) (hB : IsOmT q b eB) (hC : IsOmT q (a + b) eC)
    (g₀ h₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤)) (h : Fin b → Γ(X, ⊤)) :
    eC (cupH q rfl rfl (eA.symm (gForm q g₀ g)) (eB.symm (gForm q h₀ h))) =
      wedgeOm K (Sec q ⊤) rfl (gForm q g₀ g) (gForm q h₀ h) := by
  have e := isFormT_unique (isFormT_cup (hA g₀ g) (hB h₀ h)) (hC (g₀ * h₀) (Fin.append g h))
  rw [e, LinearEquiv.apply_symm_apply]
  exact (wedge_form (K := K) (A := Sec q ⊤) g₀ h₀ g h).symm

theorem main : ∀ {K : Type} [CommRing K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (a b c : ℕ) (h : a + b = c)
    (eA : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a) (eB : CrystallineSemistableComparison.HT.Hdg q b b ≃ₗ[K] OmU q ⊤ b) (eC : CrystallineSemistableComparison.HT.Hdg q c c ≃ₗ[K] OmU q ⊤ c),
    CrystallineSemistableComparison.Om.L2.IsOmT q a eA → CrystallineSemistableComparison.Om.L2.IsOmT q b eB → CrystallineSemistableComparison.Om.L2.IsOmT q c eC → ∀ x y,
      eC (CrystallineSemistableComparison.HT.cupH q h h x y) = wedgeOm K (Sec q ⊤) h (eA x) (eB y) := by
  intro K _ X q a b c h eA eB eC hA hB hC x y
  subst h
  obtain ⟨B, hB'⟩ := exists_bil q a b
  rw [← hB']
  refine bilin_ext eA eB eC B (wedgeOm K (Sec q ⊤) rfl) _ _ (GlobalTheory.CompanionTheory.OntoForms.formLaws K (Sec q ⊤) (Sec q ⊤) a).1
    (GlobalTheory.CompanionTheory.OntoForms.formLaws K (Sec q ⊤) (Sec q ⊤) b).1 ?_ x y
  rintro _ ⟨g₀, g, rfl⟩ _ ⟨h₀, h, rfl⟩
  rw [hB']
  exact gen_eq eA eB eC hA hB hC g₀ h₀ g h

end GlobalTheory.CompanionTheory.OmCup
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HodgeFormIsoOfBijective
section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory AlgebraicGeometry GlobalTheory.LogCris DividedPowers GlobalTheory.CechDR GlobalTheory.HodgeCoh

noncomputable section

namespace GlobalTheory.CompanionTheory.HodgeFormTop

open CrystallineSemistableComparison CrystallineSemistableComparison.Onto CrystallineSemistableComparison.HT CrystallineSemistableComparison.Om.L2 CrystallineSemistableComparison.Pb

section
variable {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K))

def omEq (a : ℕ) : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q ⊤) a ≃ₗ[K] OmU q ⊤ a := LinearEquiv.refl K (OmU q ⊤ a)

abbrev resTop (a : ℕ) := CH.Mor.restrict (G q a) (inU q ⊤).ι

theorem resTop_pullC_bij (a n : ℕ) : Function.Bijective ((resTop q a).pullC n) :=
  (topRes_pf K _ (G q a) (inU q ⊤) ⊥ (fun T => inTop q T) n).1

theorem resTop_bij (a n : ℕ) : Function.Bijective ((resTop q a).pull n) :=
  CrystallineSemistableComparison.P.mapH_bij _ (fun m => resTop_pullC_bij q a m) n

def resTopEquiv (a : ℕ) : Hdg q a a ≃ₗ[K] HV q ⊤ a a :=
  LinearEquiv.ofBijective ((resTop q a).pull a) (resTop_bij q a a)

def LiftsT.toTop (Λ : LiftsT q) : Lifts q ⊤ where
  v T g := Λ.v T.obj g
  hv T g := Λ.hv T.obj g

theorem isFormT_of_isForm {a : ℕ} (g₀ : Γ(X, ⊤)) (g : Fin a → Γ(X, ⊤)) (c : HV q ⊤ a a)
    (h : IsForm q ⊤ (a := a) g₀ g c) : IsFormT q g₀ g ((resTopEquiv q a).symm c) := by
  intro Λ
  obtain ⟨f, hf, hc, hz⟩ := h (LiftsT.toTop q Λ)
  obtain ⟨z, rfl⟩ := (resTop_pullC_bij q a a).2 f
  have hd : CH.d (G q a) a z = 0 := by
    apply (resTop_pullC_bij q a (a + 1)).1
    rw [map_zero, ← CH.Mor.d_pullC]
    exact hf
  have hcz : (resTopEquiv q a) ((CH.cx (G q a)).cls z hd) = c := by
    rw [hc]
    exact CrystallineSemistableComparison.P.mapH_cls (resTop q a).hom a z hd _
  refine ⟨z, hd, ?_, fun t => ?_⟩
  · rw [← hcz, LinearEquiv.symm_apply_apply]
  · exact hz (t ⋙ (inU q ⊤).lift (𝟭 _) (fun T => inTop q T))

end

theorem main : ∀ {K : Type} [Field K] {X : Scheme.{0}} (q : X ⟶ Spec (CommRingCat.of K)) (a : ℕ),
    (∃ e : CrystallineSemistableComparison.Onto.Om K (CrystallineSemistableComparison.Onto.Sec q ⊤) a →ₗ[K] CrystallineSemistableComparison.Onto.HV q ⊤ a a, CrystallineSemistableComparison.Onto.IsOm q ⊤ a e ∧ Function.Bijective e) →
    ∃ e' : CrystallineSemistableComparison.HT.Hdg q a a ≃ₗ[K] OmU q ⊤ a, CrystallineSemistableComparison.Om.L2.IsOmT q a e' := by
  intro K _ X q a ⟨e, he, hb⟩
  refine ⟨((resTopEquiv q a).trans (LinearEquiv.ofBijective e hb).symm).trans (omEq q a), fun g₀ g => ?_⟩
  exact isFormT_of_isForm q g₀ g _ (he g₀ g)

end GlobalTheory.CompanionTheory.HodgeFormTop
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HypothesesPreservedByLinearPullback
section
open scoped Matrix NNReal ENNReal ComplexConjugate TensorProduct
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.Pj Formalism.IndefR.Datum MeasureTheory
open GlobalTheory.AutomorphicL2Unitary GlobalTheory.AdelicU GlobalTheory.Doubling GlobalTheory.Cont GlobalTheory.MixModel GlobalTheory.StdUnn PositivityTheory.GramSchwartzFunctions PositivityTheory.GramSchwartzFunctions.BC
open GlobalTheory.IndefiniteRowSideFullHecke.ModerateGrowthSchwartz (schwartzA)
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilSiegel.Deg

variable {D : D7}

def rightMulEquiv {m r : ℕ} (a : Matrix (Fin r) (Fin r) D.host.E) (ha : a.det ≠ 0) :
    Matrix (Fin m) (Fin r) D.host.E ≃ Matrix (Fin m) (Fin r) D.host.E where
  toFun ξ := ξ * a
  invFun ξ := ξ * a⁻¹
  left_inv ξ := by
    have hu : IsUnit a.det := isUnit_iff_ne_zero.mpr ha
    simp [Matrix.mul_assoc, Matrix.mul_nonsing_inv a hu]
  right_inv ξ := by
    have hu : IsUnit a.det := isUnit_iff_ne_zero.mpr ha
    simp [Matrix.mul_assoc, Matrix.nonsing_inv_mul a hu]

theorem invPt_mul (V : HSp D) {r : ℕ} (h : GA D V) (ξ : Matrix (Fin V.rank) (Fin r) D.host.E)
    (a : Matrix (Fin r) (Fin r) D.host.E) :
    GlobalTheory.SiegelFormula.invPt V h (ξ * a) =
      HMul.hMul (GlobalTheory.SiegelFormula.invPt V h ξ) (a.map (incA D)) := by
  unfold GlobalTheory.SiegelFormula.invPt
  rw [Matrix.map_mul, Matrix.mul_assoc]

theorem absTheta_pull (V : HSp D) {r : ℕ} (φ : Mx D V.rank r → ℂ)
    (a : Matrix (Fin r) (Fin r) D.host.E) (ha : a.det ≠ 0) (h : GA D V) :
    GlobalTheory.SiegelFormula.absTheta V (pull a φ) h = GlobalTheory.SiegelFormula.absTheta V φ h := by
  unfold GlobalTheory.SiegelFormula.absTheta
  rw [← (rightMulEquiv (m := V.rank) a ha).tsum_eq
    (fun ξ => ‖φ (GlobalTheory.SiegelFormula.invPt V h ξ)‖ₑ)]
  refine tsum_congr fun ξ => ?_
  show ‖φ _‖ₑ = ‖φ (GlobalTheory.SiegelFormula.invPt V h (ξ * a))‖ₑ
  rw [invPt_mul]

theorem absThetaInt_pull (V : HSp D) (ν : Measure (GA D V)) {r : ℕ} (φ : Mx D V.rank r → ℂ)
    (a : Matrix (Fin r) (Fin r) D.host.E) (ha : a.det ≠ 0) :
    GlobalTheory.SiegelFormula.absThetaInt V ν (pull a φ) = GlobalTheory.SiegelFormula.absThetaInt V ν φ := by
  unfold GlobalTheory.SiegelFormula.absThetaInt
  have : GlobalTheory.SiegelFormula.absTheta V (pull a φ) = GlobalTheory.SiegelFormula.absTheta V φ :=
    funext (absTheta_pull V φ a ha)
  rw [this]

theorem hyp_pull : ∀ (D : D7) (r : ℕ) (V : HSp D) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D)
    (μ : Measure (Mx D V.rank r)) (lam : Measure (hermA D r)) (ν : Measure (GA D V))
    (φ : Mx D V.rank r → ℂ) (a : Matrix (Fin r) (Fin r) D.host.E), a.det ≠ 0 →
    Hyp D r V ψ θ μ lam ν φ → Hyp D r V ψ θ μ lam ν (pull a φ) := by
  intro D r V ψ θ μ lam ν φ a ha ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  have hli : LinearIndependent D.host.E a :=
    Matrix.linearIndependent_rows_of_isUnit ((Matrix.isUnit_iff_isUnit_det a).mpr (isUnit_iff_ne_zero.mpr ha))
  refine ⟨h1, h2, h3, h4, h5, h6, _root_.GlobalTheory.CompanionTheory.PullSch.pullSchLI D θ h3 _ _ _ a hli φ h7, ?_⟩
  rw [absThetaInt_pull V ν φ a ha]
  exact h8

end GlobalTheory.CompanionTheory.WeilSiegel.Deg
end
end

-- bundled from Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Imports
section
open GlobalTheory.PRep GlobalTheory.SmGL
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.SmGL.Bernstein

theorem prod₂_detRep_isIrreducible :
    (∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k],
      JacquetOfInducedFiltration k) →
    ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
      (a b : ℕ) (χ₁ χ₂ : kˣ →* ℂˣ), IsSmoothChar χ₁ → IsSmoothChar χ₂ → IsUnitaryChar χ₁ →
      IsUnitaryChar χ₂ → (a ≠ b ∨ χ₁ ≠ χ₂) →
      (prod₂ (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).IsIrreducible := by
  intro hJ k _ _ _ _ a b χ₁ χ₂ s₁ s₂ u₁ u₂ hne
  haveI := GlobalTheory.CompanionTheory.DegPrinSeries.nontrivial_subrepresentation k a b χ₁ χ₂ s₁ s₂
  show IsSimpleOrder (Subrepresentation (parInd (two (stdSum (rfl : a + b = a + b)))
    ((extTensor (detRep (Fin a) χ₁) (detRep (Fin b) χ₂)).comp (leviTwo k (Fin a) (Fin b)).symm.toMonoidHom)))
  refine ⟨fun W => ?_⟩
  obtain ⟨W', hc⟩ := _root_.GlobalTheory.CompanionTheory.UnitSemisimple.exists_isCompl _ (GlobalTheory.CompanionTheory.SmGL.exists_compact_open_subgroup_subset k (a + b))
    (GlobalTheory.CompanionTheory.DegenSeries.isAdmissible_degenerate k a b χ₁ χ₂ s₁ s₂)
    (GlobalTheory.CompanionTheory.DegenerateSeries.isUnitarisable_degenerateSeries k a b χ₁ χ₂ s₁ s₂ u₁ u₂) W
  by_contra h
  push_neg at h
  have hW' : W' ≠ ⊥ := by
    rintro rfl
    exact h.2 (eq_top_of_isCompl_bot hc)
  exact _root_.GlobalTheory.CompanionTheory.SplitFrob.not_dichotomy_det k a b χ₁ χ₂ W W' hc h.1 hW'
    (_root_.GlobalTheory.CompanionTheory.SmGL.Bernstein.mackey_maps_proportional k a b χ₁ χ₂ (hJ k) s₁ s₂ u₁ u₂ hne)

end GlobalTheory.CompanionTheory.SmGL.Bernstein
end

