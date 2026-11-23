module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0010
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0003
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0198
public import Development.AbelianVarietyTheory.Definitions.Foundations.NotCoboundaryConstantOne
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0006
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0086
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0199
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsInvariantLift
public import Development.AbelianVarietyTheory.Definitions.Foundations.IsSatVecUOfIsSphericalU
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricLevelH1Coboundary

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CupKummerDlogModPrimePowLevelL
section
noncomputable section

namespace GlobalTheory.K5.LevelDown

open Polynomial GlobalTheory.K5 GlobalTheory.K5.Basic

variable {p : ℕ} [hp : Fact p.Prime] {Ω : Type*} [Field Ω] [Algebra (O0 p) Ω]

theorem mem_adjoin (L : ℕ) (x : On p L) : x ∈ Algebra.adjoin (O0 p) {xn p L, yn p L} := by
  obtain ⟨f, rfl⟩ := Ideal.Quotient.mk_surjective x
  set S := Algebra.adjoin (O0 p) {xn p L, yn p L}
  have hx : xn p L ∈ S := Algebra.subset_adjoin (by simp)
  have hy : yn p L ∈ S := Algebra.subset_adjoin (by simp)
  have hb : ∀ b : O0 p, Ideal.Quotient.mk (towerIdeal p L) (C (C b)) ∈ S := by
    intro b
    have : Ideal.Quotient.mk (towerIdeal p L) (C (C b)) = algebraMap (O0 p) (On p L) b := rfl
    rw [this]; exact S.algebraMap_mem b
  have hC : ∀ a : Polynomial (O0 p), Ideal.Quotient.mk (towerIdeal p L) (C a) ∈ S := by
    intro a
    induction a using Polynomial.induction_on with
    | C b => exact hb b
    | add f g hf hg =>
      rw [C_add, (Ideal.Quotient.mk (towerIdeal p L)).map_add]
      exact S.add_mem hf hg
    | monomial k b _ =>
      rw [C_mul, C_pow, map_mul, map_pow]
      exact S.mul_mem (hb b) (S.pow_mem hx _)
  induction f using Polynomial.induction_on with
  | C a => exact hC a
  | add f g hf hg =>
    rw [(Ideal.Quotient.mk (towerIdeal p L)).map_add]
    exact S.add_mem hf hg
  | monomial k a _ => rw [map_mul, map_pow]; exact S.mul_mem (hC a) (S.pow_mem hy _)

theorem zeta_pow_sub (T : GlobalTheory.K5.Tower p Ω) (m k : ℕ) : T.ζ (m + k) ^ p ^ k = T.ζ m := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_mul, ← add_assoc, T.ζpow, ih]

theorem qq_pow_sub (T : GlobalTheory.K5.Tower p Ω) (m k : ℕ) : T.qq (m + k) ^ p ^ k = T.qq m := by
  induction k with
  | zero => simp
  | succ k ih => rw [pow_succ', pow_mul, ← add_assoc, T.qpow, ih]

theorem isInt_nat (m : ℕ) : IsInt (p := p) (m : Ω) := by
  rw [IsInt, ← map_natCast (algebraMap (O0 p) Ω)]; exact isIntegral_algebraMap

theorem isInt_emb (T : GlobalTheory.K5.Tower p Ω) (L : ℕ) (ι : On p L →ₐ[O0 p] Ω) (hι : IsEmb T L ι)
    (x : On p L) : IsInt (p := p) (ι x) := by
  have h : Algebra.adjoin (O0 p) {xn p L, yn p L} ≤ (integralClosure (O0 p) Ω).comap ι := by
    rw [Algebra.adjoin_le_iff]
    rintro z (rfl | rfl)
    · show ι (xn p L) ∈ integralClosure (O0 p) Ω
      rw [mem_integralClosure_iff, hι.1]
      exact IsIntegral.of_pow (pow_pos hp.out.pos L) (by rw [(T.prim L).pow_eq_one]; exact isIntegral_one)
    · show ι (yn p L) ∈ integralClosure (O0 p) Ω
      rw [mem_integralClosure_iff, hι.2]
      refine IsIntegral.of_pow (pow_pos hp.out.pos L) ?_
      rw [qq_pow]; exact isIntegral_algebraMap
  exact h (mem_adjoin L x)

theorem fix_emb (T : GlobalTheory.K5.Tower p Ω) (L : ℕ) (ι : On p L →ₐ[O0 p] Ω) (hι : IsEmb T L ι)
    (g : Gal p Ω) (hg : g ∈ Gn T L) (x : On p L) : g (ι x) = ι x := by
  have hg' := (mem_gn T L g).1 hg
  have h : Algebra.adjoin (O0 p) {xn p L, yn p L} ≤
      AlgHom.equalizer ((g : Ω →ₐ[O0 p] Ω).comp ι) ι := by
    rw [Algebra.adjoin_le_iff]
    rintro z (rfl | rfl)
    · show g (ι (xn p L)) = ι (xn p L)
      rw [hι.1]; exact hg'.1
    · show g (ι (yn p L)) = ι (yn p L)
      rw [hι.2]; exact hg'.2
  exact h (mem_adjoin L x)

theorem cong_mono {k m : ℕ} (h : k ≤ m) {x y : Ω}
    (hc : Cong (p := p) m x y) : Cong (p := p) k x y := by
  obtain ⟨z, hz, e⟩ := hc
  refine ⟨(p : Ω) ^ (m - k) * z, IsIntegral.mul (IsIntegral.pow (isInt_nat p) _) hz, ?_⟩
  rw [e, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]

theorem locallyConstantModPrimePow_of_le {k m : ℕ} (h : k ≤ m) {w : Gal p Ω → Ω} (hw : LocallyConstantOneCochain m w) : LocallyConstantOneCochain k w :=
  ⟨hw.1, fun g => by
    obtain ⟨S, hS⟩ := hw.2 g
    exact ⟨S, fun h' hh => cong_mono h (hS h' hh)⟩⟩

theorem cong_mul' {k : ℕ} {x y x' y' : Ω} (h : Cong (p := p) k x y) (h' : Cong (p := p) k x' y')
    (hx' : IsInt (p := p) x') (hy : IsInt (p := p) y) : Cong (p := p) k (x * x') (y * y') := by
  obtain ⟨a, ha, e⟩ := h
  obtain ⟨b, hb, e'⟩ := h'
  exact ⟨a * x' + y * b, (ha.mul hx').add (hy.mul hb), by linear_combination x' * e + y * e'⟩

theorem kum_down (T : GlobalTheory.K5.Tower p Ω) {n L : ℕ} (hnL : n ≤ L) {H : Subgroup (Gal p Ω)} {R : Ω}
    (hR : R ≠ 0) {aL : Gal p Ω → ZMod (p ^ L)} (haL : IsKum T L H R aL)
    {a : Gal p Ω → ZMod (p ^ n)} (ha : IsKum T n H (R ^ p ^ (L - n)) a) {g : Gal p Ω}
    (hg : g ∈ H) : (a g).val ≡ (aL g).val [MOD p ^ n] := by
  have e1 := ha g hg
  rw [map_pow, haL g hg, mul_pow, ← pow_mul, mul_comm ((aL g).val), pow_mul] at e1
  have hz : T.ζ L ^ p ^ (L - n) = T.ζ n := by
    have := zeta_pow_sub T n (L - n); rwa [Nat.add_sub_cancel' hnL] at this
  rw [hz] at e1
  have e2 := mul_right_cancel₀ (pow_ne_zero _ hR) e1
  exact ((zeta_pow_eq_iff T n _ _).1 e2).symm

end GlobalTheory.K5.LevelDown

open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

theorem GlobalTheory.K5.LevelDown.cup_kummer_dlog_mod : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → 1 ≤ n → ∀ ι : On p L →ₐ[O0 p] Ω, IsEmb T L ι →
  ∀ (u v : (On p L)ˣ) (α β α' β' : On p L), IsDlog p L (u : On p L) α β → IsDlog p L (v : On p L) α' β' →
  ∀ r s : Ω, r ^ (p ^ n) = ι u → s ^ (p ^ n) = ι v →
  ∀ a b lz lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Gn T L) r a → IsKum T n (Gn T L) s b → IsKum T n (Gn T L) (T.ζ (L + n)) lz → IsKum T n (Gn T L) (T.qq (L + n)) lq →
  Cob2 n (Gn T L) (fun g h => (p : Ω) ^ c * (((a g).val : Ω) * ((b h).val : Ω)) + (p : Ω) ^ c * ι (α * β' - β * α') * (((lz g).val : Ω) * ((lq h).val : Ω))) := by
  intro p _ hp2
  obtain ⟨c, hc⟩ := _root_.GlobalTheory.K5.KummerCup.cup_kummer_dlog p hp2
  refine ⟨c, ?_⟩
  intro Ω _ _ hclo T L n hnL hn ι hι u v α β α' β' hu hv r s hr hs a b lz lq ha hb hlz hlq
  have := hclo.clo
  have hpr : p.Prime := Fact.out
  have hL : 1 ≤ L := le_trans hn hnL
  have hpos : ∀ k, 0 < p ^ k := fun k => pow_pos hpr.pos k
  have hunit : ∀ w : (On p L)ˣ, ι (w : On p L) ≠ 0 := fun w h => by
    have := congrArg ι w.mul_inv
    rw [map_mul, h, zero_mul, map_one] at this
    exact zero_ne_one this
  have hroot : ∀ (w : (On p L)ˣ) (x : Ω), x ^ p ^ n = ι (w : On p L) → ∃ X : Ω, X ≠ 0 ∧
      X ^ p ^ (L - n) = x ∧ X ^ p ^ L = (T.ζ L - 1) ^ (0 : ℤ) * ι (w : On p L) := by
    intro w x hx
    obtain ⟨X, hX⟩ := IsAlgClosed.exists_pow_nat_eq x (hpos (L - n))
    refine ⟨X, ?_, hX, ?_⟩
    · rintro rfl
      rw [zero_pow (pow_ne_zero _ hpr.ne_zero)] at hX
      rw [← hX, zero_pow (pow_ne_zero _ hpr.ne_zero)] at hx
      exact hunit w hx.symm
    · rw [zpow_zero, one_mul, ← hx, ← hX, ← pow_mul, ← pow_add, Nat.sub_add_cancel hnL]
  obtain ⟨R, hR0, hR, hRL⟩ := hroot u r hr
  obtain ⟨S, hS0, hS, hSL⟩ := hroot v s hs
  have hfix := LevelDown.fix_emb T L ι hι
  have hgn := fun g (hg : g ∈ Gn T L) => (Basic.mem_gn T L g).1 hg
  obtain ⟨aL, haL⟩ := Basic.exists_isKum T L (Gn T L) hR0 (fun g hg => by
    rw [hRL, zpow_zero, one_mul]; exact hfix g hg _)
  obtain ⟨bL, hbL⟩ := Basic.exists_isKum T L (Gn T L) hS0 (fun g hg => by
    rw [hSL, zpow_zero, one_mul]; exact hfix g hg _)
  have hZ0 : T.ζ (2 * L) ≠ 0 := (T.prim _).ne_zero (pow_ne_zero _ hpr.ne_zero)
  have hZL : T.ζ (2 * L) ^ p ^ L = T.ζ L := by
    rw [two_mul]; exact LevelDown.zeta_pow_sub T L L
  have hQL : T.qq (2 * L) ^ p ^ L = T.qq L := by
    rw [two_mul]; exact LevelDown.qq_pow_sub T L L
  obtain ⟨zL, hzL⟩ := Basic.exists_isKum T L (Gn T L) hZ0 (fun g hg => by
    rw [hZL]; exact (hgn g hg).1)
  obtain ⟨qL, hqL⟩ := Basic.exists_isKum T L (Gn T L) (Basic.qq_ne_zero T _) (fun g hg => by
    rw [hQL]; exact (hgn g hg).2)
  obtain ⟨w, hw, hcong⟩ := hc Ω hclo T L hL ι hι 0 0 u v α β α' β' hu hv R S hRL hSL aL bL zL qL
    haL hbL hzL hqL
  have e2 : L + n + (L - n) = 2 * L := by omega
  have hZn : T.ζ (2 * L) ^ p ^ (L - n) = T.ζ (L + n) := by
    rw [← e2]; exact LevelDown.zeta_pow_sub T (L + n) (L - n)
  have hQn : T.qq (2 * L) ^ p ^ (L - n) = T.qq (L + n) := by
    rw [← e2]; exact LevelDown.qq_pow_sub T (L + n) (L - n)
  have hX : ι (fPi p L 0 0 α β α' β') / (T.ζ L - 1) = ι (α * β' - β * α') := by
    have hne : T.ζ L - 1 ≠ 0 :=
      sub_ne_zero.2 ((T.prim L).ne_one (Nat.one_lt_pow (by omega) hpr.one_lt))
    rw [div_eq_iff hne]
    have : fPi p L 0 0 α β α' β' = (xn p L - 1) * (α * β' - β * α') := by
      simp only [fPi]; push_cast; ring
    rw [this, map_mul, map_sub, hι.1, map_one]; ring
  refine ⟨w, LevelDown.locallyConstantModPrimePow_of_le hnL hw, fun g hg h hh => ?_⟩
  refine Basic.cong_trans ?_ (LevelDown.cong_mono hnL (hcong g hg h hh))
  beta_reduce
  rw [hX]
  have hA : Cong (p := p) n ((a g).val : Ω) ((aL g).val : Ω) := Basic.cong_natCast
    (LevelDown.kum_down T hnL hR0 haL (by rw [hR]; exact ha) hg)
  have hB : Cong (p := p) n ((b h).val : Ω) ((bL h).val : Ω) := Basic.cong_natCast
    (LevelDown.kum_down T hnL hS0 hbL (by rw [hS]; exact hb) hh)
  have hC : Cong (p := p) n ((lz g).val : Ω) ((zL g).val : Ω) := Basic.cong_natCast
    (LevelDown.kum_down T hnL hZ0 hzL (by rw [hZn]; exact hlz) hg)
  have hD : Cong (p := p) n ((lq h).val : Ω) ((qL h).val : Ω) := Basic.cong_natCast
    (LevelDown.kum_down T hnL (Basic.qq_ne_zero T _) hqL (by rw [hQn]; exact hlq) hh)
  have iN := fun m : ℕ => (LevelDown.isInt_nat (p := p) (Ω := Ω) m)
  have iP : IsInt (p := p) ((p : Ω) ^ c) := IsIntegral.pow (iN p) c
  have iX : IsInt (p := p) (ι (α * β' - β * α')) := LevelDown.isInt_emb T L ι hι _
  refine Basic.cong_add ?_ ?_
  · exact LevelDown.cong_mul' (Basic.cong_refl _ _)
      (LevelDown.cong_mul' hA hB (iN _) (iN _)) ((iN _).mul (iN _)) iP
  · exact LevelDown.cong_mul' (Basic.cong_refl _ _)
      (LevelDown.cong_mul' hC hD (iN _) (iN _)) ((iN _).mul (iN _)) (iP.mul iX)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFunctionalValueModPrimePowUniqueOddWeight
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory

theorem isThB_coeff_cong : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε)
    (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) →
    l ≠ 2 → ¬ l ∣ N → 1 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n w : ℕ), Odd w → ∀ b : X.Fn l, b ∈ X.B N l w →
    ∀ φ φ' : HahnSeries ℚ Ω,
  IsThB X A N l n b φ → IsThB X A N l n b φ' → ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  intro Ω _ _ _ ε X A N l _ _ hl2 hlN hN hlA n w _ b _ φ φ' h h' r
  obtain ⟨f, hfinv, hfcls, hfδ, hfdl⟩ := h
  obtain ⟨f', hf'inv, hf'cls, hf'δ, hf'dl⟩ := h'
  obtain ⟨u, hu⟩ := Tower.cls_eq_pow X l n f f' (hfcls.symm.trans hf'cls)
  have hL : 0 < l ^ n := pow_pos (Fact.out : l.Prime).pos n
  have hfne : (f : X.K) ≠ 0 := f.ne_zero
  have hune : (u : X.K) ≠ 0 := u.ne_zero
  have hpow : (u : X.K) ^ (l ^ n) = (f' : X.K) * (f : X.K)⁻¹ := by
    rw [hu]; field_simp
  have hinv : Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) ((u : X.K) ^ (l ^ n)) := by
    intro γ hγ
    rw [hpow, map_mul, map_inv₀, hfinv γ hγ, hf'inv γ hγ]
  have hT : X.sl (ofSL ModularGroup.T) (u : X.K) = u := by
    refine TInv.sl_T_eq X N l n (Fact.out) hl2 hlN hN u hune hinv ?_
    intro δ hδ hδ'
    obtain ⟨g, hg, hfg⟩ := hfδ δ hδ hδ'
    obtain ⟨g', hg', hfg'⟩ := hf'δ δ hδ hδ'
    have hgne : g ≠ 0 := by
      rintro rfl
      rw [zero_pow hL.ne'] at hfg
      exact mul_ne_zero hfne ((map_ne_zero _).2 hfne) hfg
    refine ⟨g' * g⁻¹, ?_, ?_⟩
    · intro γ hγ
      rw [map_mul, map_inv₀, hg γ hγ, hg' γ hγ]
    · have hsf : X.sl (ofSL δ) (f : X.K) ≠ 0 := (map_ne_zero _).2 hfne
      rw [mul_pow g', inv_pow, ← hfg, ← hfg', hu, map_mul, map_pow]
      field_simp
      ring
  have : Algebra.IsAlgebraic ℚ Ω := DlPow.isAlgebraic_of_tower X
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, inferInstance⟩
  rw [hu] at hf'dl
  exact DlPow.isDl_mul_lpow_cong X A l hlA n f u hfne hune hT φ φ' hfdl hf'dl r

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCuspFunctionalOddWeightOddPrime
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups

namespace GlobalTheory.ThEx

theorem T_mem_Gamma1 (M : ℕ) : ModularGroup.T ∈ CongruenceSubgroup.Gamma1 M := by
  rw [CongruenceSubgroup.Gamma1_mem]
  simp [ModularGroup.T]

theorem of_lift (hlift : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime], l ≠ 2 → ¬ l ∣ N → 1 ≤ N → ∀ (n w : ℕ), Odd w → ∀ b : X.Fn l, b ∈ X.B N l w → ∃ f : X.Kˣ, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) (f : X.K) ∧ AdicCompletion.eval (idl l) (X.Kl l) n (b ![1, 0]) = X.cls l n f ∧ (∀ δ ∈ CongruenceSubgroup.Gamma1 N, -δ ∈ CongruenceSubgroup.Gamma (l ^ n) → ∃ g : X.K, Inv X (CongruenceSubgroup.Gamma1 (N * l ^ n)) g ∧ (f : X.K) * X.sl (ofSL δ) f = g ^ (l ^ n))) : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], Algebra.IsAlgebraic ℚ Ω → (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → ¬ l ∣ N → 1 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n w : ℕ), Odd w → ∀ b : X.Fn l, b ∈ X.B N l w → ∃ φ : HahnSeries ℚ Ω, IsThB X A N l n b φ ∧ IsLat 1 φ := by
  intro Ω _ _ _ ε X A N l _ halg han hl2 hlN hN hA n w hw b hb
  have : IsAlgClosure ℚ Ω := ⟨inferInstance, halg⟩
  obtain ⟨f, hfinv, hfcls, hfsq⟩ := hlift Ω ε X N l hl2 hlN hN n w hw b hb
  obtain ⟨ψ, hψan, hψd⟩ := han
  have hT : (f : X.K) ∈ GlobalTheory.Glue.KT X 1 := by
    rw [GlobalTheory.Glue.KT.mem_def, pow_one]
    exact hfinv _ (T_mem_Gamma1 _)
  obtain ⟨φ, hdl, hden⟩ := GlobalTheory.dl_exists ε X ⟨ψ, hψd, hψan⟩ l A hA n 1 (f : X.K) one_pos f.ne_zero hT
  refine ⟨φ, ⟨f, hfinv, hfcls, hfsq, by simpa using hdl⟩, fun r hr => ?_⟩
  simpa using hden r hr

theorem thex : ∀ (Ω : Type) [Field Ω] [Algebra ℚ Ω] [IsAlgClosed Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (A : ValuationSubring Ω) (N l : ℕ) [Fact l.Prime], Algebra.IsAlgebraic ℚ Ω → (∃ φ : ℂ → ℂ, X.an X.jK = (φ : Mero) ∧ DifferentiableOn ℂ φ Hs) → l ≠ 2 → ¬ l ∣ N → 5 ≤ N → ((l : Ω) ∈ A.nonunits) → ∀ (n w : ℕ), Odd w → ∀ b : X.Fn l, b ∈ X.B N l w → ∃ φ : HahnSeries ℚ Ω, IsThB X A N l n b φ ∧ IsLat 1 φ := by
  intro Ω _ _ _ ε X A N l _ halg han hl2 hlN hN hA n w hw b hb
  exact of_lift (GlobalTheory.ThLift.exists_invariant_lift) Ω ε X A N l halg han hl2 hlN (by omega) hA n w hw b hb

end GlobalTheory.ThEx
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMultisetSatakeEigenvalueEq
section
open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

namespace GlobalTheory.LFun


open Polynomial in
theorem exists_multiset_esymm_eq (n : ℕ) (e : ℕ → ℂ) (h0 : e 0 = 1) (hn : e n ≠ 0) :
    ∃ A : Multiset ℂ, A.card = n ∧ (0 : ℂ) ∉ A ∧ ∀ j ≤ n, A.esymm j = e j := by
  set p : ℂ[X] := ∑ k ∈ Finset.range (n + 1), monomial k ((-1) ^ (n - k) * e (n - k)) with hp
  have hc : ∀ k, p.coeff k = if k ≤ n then (-1) ^ (n - k) * e (n - k) else 0 := fun k => by
    rw [hp, finsetSum_coeff]
    simp only [coeff_monomial_apply, Finset.sum_ite_eq', Finset.mem_range, Nat.lt_succ_iff]
  have hle : p.natDegree ≤ n := natDegree_le_iff_coeff_eq_zero.2 fun k hk => by rw [hc, if_neg (by omega)]
  have hcn : p.coeff n = 1 := by simp [hc, h0]
  have hd : p.natDegree = n := natDegree_eq_of_le_of_coeff_ne_zero hle (by simp [hcn])
  have hl : p.leadingCoeff = 1 := by rw [leadingCoeff, hd, hcn]
  have hr : p.roots.card = p.natDegree := (IsAlgClosed.splits p).natDegree_eq_card_roots.symm
  refine ⟨p.roots, hr.trans hd, fun hz => ?_, fun j hj => ?_⟩
  · have := isRoot_of_mem_roots hz
    rw [IsRoot, ← coeff_zero_eq_eval_zero, hc] at this
    simp [hn] at this
  · have := coeff_eq_esymm_roots_of_card hr (k := n - j) (by omega)
    rw [hc, if_pos (by omega), hl, hd, one_mul, Nat.sub_sub_self hj] at this
    exact (mul_left_cancel₀ (pow_ne_zero _ (by norm_num)) this).symm

theorem exists_satEig_eq : ∀ (q n : ℕ), q ≠ 0 → ∀ c : ℕ → ℂ, c 0 = 1 → c n ≠ 0 →
    ∃ B : Multiset ℂˣ, B.card = n ∧ ∀ j ≤ n, satEig q n B j = c j := by
  intro q n hq c h0 hn
  have hw : ∀ j : ℕ, (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2) ≠ 0 := fun j h =>
    hq (by exact_mod_cast ((Complex.cpow_eq_zero_iff _ _).1 h).1)
  obtain ⟨A, hA, hz, he⟩ := exists_multiset_esymm_eq n
    (fun j => c j / (q : ℂ) ^ (((j : ℂ) * ((n : ℂ) - j)) / 2)) (by simp [h0]) (div_ne_zero hn (hw n))
  refine ⟨A.pmap (fun a (h : a ≠ 0) => Units.mk0 a h) (fun a ha h => hz (h ▸ ha)), by simp [hA], fun j hj => ?_⟩
  rw [satEig, Multiset.map_pmap]
  simp only [Units.val_mk0, Multiset.pmap_eq_map, Multiset.map_id']
  rw [he j hj]
  exact mul_div_cancel₀ _ (hw j)

end GlobalTheory.LFun
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.GeometricLevelH1CoboundaryStatement
section
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.geometric_level_h1_coboundary : ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ∃ c : ℕ, ∀ (Ω : Type) [Field Ω] [Algebra (O0 p) Ω], IsClo p Ω → ∀ (T : GlobalTheory.K5.Tower p Ω) (L n : ℕ), n ≤ L → ∀ lq : Gal p Ω → ZMod (p ^ n), IsKum T n (Ggeo p Ω ⊓ Gn T L) (T.qq (L + n)) lq →
  (∀ a : Gal p Ω → Ω, IntegralLocallyConstCochainModPow n (Ggeo p Ω ⊓ Gn T L) a → (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), ∀ h ∈ (Ggeo p Ω ⊓ Gn T L), Cong (p := p) n (a (g * h)) (a g + g (a h))) →
    ∃ o : Ω, IsInt (p := p) o ∧ (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), g o = o) ∧ Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun g => (p : Ω) ^ c * a g - o * ((lq g).val : Ω))) ∧
  (∀ o : Ω, IsInt (p := p) o → (∀ g ∈ (Ggeo p Ω ⊓ Gn T L), g o = o) → Cob1 n (Ggeo p Ω ⊓ Gn T L) (fun g => o * ((lq g).val : Ω)) → Cong (p := p) n ((p : Ω) ^ c * o) 0) := by
  exact @GlobalTheory.K5.Reb.h1_geometric_level_coboundary
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed
section
noncomputable section

namespace GlobalTheory.LFun.SatCompare

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V} {K : Subgroup G}
  {f f' : G → ℂ} {x : V}

theorem hAct_orbit (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (ρ : Representation ℂ G V) (x : V) (g : G) :
    hAct K f (fun y => ρ y x) g = ρ g (heckeVec ρ K f x) := by
  refine Eq.symm (((ρ g).toAddMonoidHom.map_finsum (finite_heckeVec hK hf ρ x)).trans (finsum_congr fun c => ?_))
  simp

theorem orbit_mem_amf (hx : x ∈ fixed ρ K) :
    (fun y => ρ y x) ∈ AMF ℂ ⊥ K (Representation.trivial ℂ (⊥ : Subgroup G) V) := by
  intro γ g κ
  have : (γ : G) = 1 := Subgroup.mem_bot.1 γ.2
  simp [this, GlobalTheory.LGrp.mem_fixed.1 hx κ κ.2]

theorem heckeVec_mem_fixed (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (hx : x ∈ fixed ρ K) :
    heckeVec ρ K f x ∈ fixed ρ K := by
  refine GlobalTheory.LGrp.mem_fixed.2 fun k hk => ?_
  have := Final.HeckeActMem G ⊥ K ℂ V _ hK f hf _ (orbit_mem_amf hx) 1 1 ⟨k, hk⟩
  simpa [hAct_orbit hK hf] using this

theorem heckeVec_conv (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (hf' : f' ∈ Hecke ℂ K) (hx : x ∈ fixed ρ K) :
    heckeVec ρ K (conv K f f') x = heckeVec ρ K f (heckeVec ρ K f' x) := by
  have := congrFun (Final.HeckeActMul G ⊥ K ℂ V _ hK f hf f' hf' _ (orbit_mem_amf hx)) 1
  rw [funext (hAct_orbit hK hf' ρ x), hAct_orbit hK hf,
    hAct_orbit hK (Final.HeckeConvMem G K ℂ hK f hf f' hf')] at this
  simpa using this

theorem heckeVec_one (hK : IsCommensurated K) (hx : x ∈ fixed ρ K) : heckeVec ρ K (dosetInd ℂ K 1) x = x := by
  have := congrFun (Final.HeckeActOne G ⊥ K ℂ V _ _ (orbit_mem_amf hx)) 1
  rw [hAct_orbit hK (Final.DosetIndMem G K ℂ 1)] at this
  simpa using this

theorem heckeVec_add_left (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (hf' : f' ∈ Hecke ℂ K) (x : V) :
    heckeVec ρ K (f + f') x = heckeVec ρ K f x + heckeVec ρ K f' x := by
  unfold heckeVec
  rw [← finsum_add_distrib (finite_heckeVec hK hf ρ x) (finite_heckeVec hK hf' ρ x)]
  exact finsum_congr fun c => by simp [add_smul]

theorem heckeVec_smul_left (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (c : ℂ) (x : V) :
    heckeVec ρ K (c • f) x = c • heckeVec ρ K f x := by
  unfold heckeVec
  rw [smul_finsum' c (finite_heckeVec hK hf ρ x)]
  exact finsum_congr fun c => by simp [mul_smul]

theorem heckeVec_zero_left (x : V) : heckeVec ρ K 0 x = 0 := by simp [heckeVec]

def heckeLin (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (ρ : Representation ℂ G V) : V →ₗ[ℂ] V where
  toFun := heckeVec ρ K f
  map_add' x y := by
    unfold heckeVec
    rw [← finsum_add_distrib (finite_heckeVec hK hf ρ x) (finite_heckeVec hK hf ρ y)]
    exact finsum_congr fun c => by simp
  map_smul' c x := (map_heckeVec hK hf (c • LinearMap.id) (fun g y => by simp) x).symm

@[simp] theorem heckeLin_apply (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (x : V) :
    heckeLin hK hf ρ x = heckeVec ρ K f x := rfl

theorem heckeVec_smul (hK : IsCommensurated K) (hf : f ∈ Hecke ℂ K) (c : ℂ) (x : V) :
    heckeVec ρ K f (c • x) = c • heckeVec ρ K f x := (heckeLin hK hf ρ).map_smul c x

end GlobalTheory.LFun.SatCompare

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LogDerivQExpansionMulPrimePowCongrStatement
section
open GlobalTheory.KZ GlobalTheory.CyclotomicQExpansion GlobalTheory.Glue
open scoped MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.logDerivQExpansion_mul_primePow_congr : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (A : ValuationSubring Ω) (l : ℕ) [Fact l.Prime], (l : Ω) ∈ A.nonunits → ∀ (n : ℕ) (f u : X.K), f ≠ 0 → u ≠ 0 → X.sl (ofSL ModularGroup.T) u = u → ∀ φ φ' : HahnSeries ℚ Ω, IsDl X A l n 1 f φ → IsDl X A l n 1 (f * u ^ (l ^ n)) φ' → ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  intro Ω _ _ _
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed ℚ
  exact @GlobalTheory.Glue.DlPow.isDl_mul_lpow_cong Ω _ _ _
end

