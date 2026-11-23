module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.KatoTwistedClassNormCompatibleCyclotomic
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle0001
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0349
public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0354
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0075
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SPushPsi
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.Bundle0002
public import Development.AutomorphicArithmetic.CyclotomicBounds.ClassNumberBounds.TotallyRealRoots.Bundle0002

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.RepSlD
section
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

section

variable {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime] (n N : ℕ)

private theorem rep_slD (f : X.Kˣ) :
    Rep X l n (slU X (toGQ !![(N : ℤ), 0; 0, 1]) f) (clsK X l n (slD X N (f : X.K))) :=
  (sCls Ω ε X l n).1 (slU X (toGQ !![(N : ℤ), 0; 0, 1]) f)

private theorem cgr_rfl {K : Type} [Field K] (m : ℕ) (f : Kˣ) : Cgr m f f := ⟨1, by simp⟩

private theorem term_mul (a a' b b' : X.Kˣ) (h : Cgr (l ^ n) a (a' * b / b')) :
    AdicCompletion.eval (idl l) (X.Kl l) n (clsK X l n (slD X N (a : X.K)) -
      (clsK X l n (slD X N (a' : X.K)) + (clsK X l n (slD X N (b : X.K)) - clsK X l n (slD X N (b' : X.K))))) = 0 := by
  obtain ⟨-, hr2, -, hr4, -⟩ := sCls Ω ε X l n
  have ra := rep_slD X l n N a
  have ra' := rep_slD X l n N a'
  have rb := rep_slD X l n N b
  have rb' := rep_slD X l n N b'
  have r1 := (hr2 _ _ _ _ ra' rb).1
  have r2 := (hr2 _ _ _ _ r1 rb').2
  obtain ⟨k, hk⟩ := h
  have hz := hr4 _ _ _ _ ra r2 ⟨slU X (toGQ !![(N : ℤ), 0; 0, 1]) k, by
    rw [hk, map_mul, map_pow, map_div, map_mul]⟩
  rw [add_sub_assoc] at hz
  exact hz

private theorem term_pow (a : X.Kˣ) (k : ℕ) :
    AdicCompletion.eval (idl l) (X.Kl l) n (clsK X l n (slD X N ((a ^ k : X.Kˣ) : X.K)) -
      (k : ℤ_[l]) • clsK X l n (slD X N (a : X.K))) = 0 := by
  obtain ⟨-, -, h3, h4, -⟩ := sCls Ω ε X l n
  refine h4 _ _ _ _ (rep_slD X l n N (a ^ k)) (h3 _ _ k (rep_slD X l n N a)) ?_
  rw [map_pow]
  exact cgr_rfl _ _

private theorem term_red (a : X.Kˣ) :
    AdicCompletion.eval (idl l) (X.Kl l) n (clsK X l (n + 1) (slD X N (a : X.K)) - clsK X l n (slD X N (a : X.K))) = 0 := by
  obtain ⟨-, -, -, h4, -, h6, -⟩ := sCls Ω ε X l n
  exact h4 _ _ _ _ (h6 _ _ (rep_slD X l (n + 1) N a)) (rep_slD X l n N a) (cgr_rfl _ _)

end

private theorem fib {ι κ V : Type} [Fintype ι] [Fintype κ] [AddCommMonoid V] (C : ι → Prop) (d : ι → κ) (Q : κ → Prop) (F : ι → V)
    [DecidablePred Q] [DecidablePred fun i => C i ∧ Q (d i)] [∀ z, DecidablePred fun i => C i ∧ d i = z] :
    ∑ i ∈ Finset.univ.filter (fun i => C i ∧ Q (d i)), F i =
      ∑ z ∈ Finset.univ.filter Q, ∑ i ∈ Finset.univ.filter (fun i => C i ∧ d i = z), F i := by
  rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ.filter (fun i => C i ∧ Q (d i))) (t := Finset.univ.filter Q) (g := d)
    (fun i hi => by simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hi ⊢; exact hi.2)]
  refine Finset.sum_congr rfl fun z hz => Finset.sum_congr ?_ fun _ _ => rfl
  ext i
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hz ⊢
  constructor
  · rintro ⟨⟨h1, -⟩, h2⟩
    exact ⟨h1, h2⟩
  · rintro ⟨h1, h2⟩
    exact ⟨⟨h1, h2 ▸ hz⟩, h2⟩

theorem UpperTheory.V.Z.Kato.Nb.sXiMul :
    UpperTheory.V.Z.Kato.Nb.SXiMul := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL x y hxy P
  have hOk : ∀ m : GL (Fin 2) (ZMod M), m ∈ Finset.univ.filter
      (fun m : GL (Fin 2) (ZMod M) => Cnd l N g (m : Matrix (Fin 2) (Fin 2) (ZMod M)) ∧
        P (Matrix.GeneralLinearGroup.det m)) →
      Ok (x ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M))) (y ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M))) :=
    fun m hm => (sCdFacts N M₀ M (Lev.eq hL)).2.2.1 m (Finset.mem_filter.1 hm).2.1.1 x y hxy
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro a a' b b' hab u
    simp only [Pi.add_apply, Pi.sub_apply]
    unfold Xi
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, map_sum]
    apply Finset.sum_eq_zero
    intro m hm
    rw [← smul_sub, ← smul_add, ← smul_sub, map_smul,
      term_mul X l n N _ _ _ _ (hab _ _ (hOk m hm)), smul_zero]
  · intro a k u
    simp only [Pi.sub_apply, Pi.smul_apply]
    unfold Xi
    beta_reduce
    set_option synthInstance.maxHeartbeats 100000 in
      rw [Finset.smul_sum, ← Finset.sum_sub_distrib, map_sum]
    apply Finset.sum_eq_zero
    intro m _
    rw [smul_comm (k : ℤ_[l]), ← smul_sub, map_smul, term_pow, smul_zero]
  · intro a u
    unfold Xi
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← Finset.sum_sub_distrib, map_sum]
    apply Finset.sum_eq_zero
    intro m _
    rw [← smul_sub, map_smul, term_red, smul_zero]
  · intro a A π t _
    funext u
    rw [Finset.sum_apply]
    unfold Xi
    convert fib (fun m : GL (Fin 2) (ZMod M) => Cnd l N g (m : Matrix (Fin 2) (Fin 2) (ZMod M)))
      (fun m => Matrix.GeneralLinearGroup.det m) (fun z => π z = t) _
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SEsT
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal UpperTheory.V GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.KZ.ES
open scoped Matrix MatrixGroups Pointwise

theorem UpperTheory.V.Z.Kato.Nb.sEsT : UpperTheory.V.Z.Kato.Nb.SEsT := by
  intro Ω _ _ _ ε X l _ N w q M hN hq hqlN hqM hM γ hγ b hb
  have hb' : ∀ g ∈ Gam N l, X.act l ↑g b = b := by
    unfold Tower.BSet at hb
    exact hb.2
  have hN0 : N ≠ 0 := by omega
  have hl0 : l ≠ 0 := (Fact.out : Nat.Prime l).ne_zero
  have hqN : q.Coprime N := (Nat.coprime_mul_iff_right.mp hqlN).2
  have hSD := Betti.isDiam_sgD (l := l) hN0 hl0 hqN
  unfold IsDiam at hSD
  obtain ⟨hSmem, hSq⟩ := hSD
  obtain ⟨hS0N, hS0l⟩ := Subgroup.mem_inf.mp hSmem
  rw [CongruenceSubgroup.Gamma0_mem] at hS0N hS0l
  unfold en at hSq
  unfold DiagMod at hγ
  obtain ⟨-, hγc, hγd⟩ := hγ
  unfold en at hγc hγd
  have hNM : N ∣ M := (dvd_mul_left N l).trans hM
  have hlM : l ∣ M := (dvd_mul_right l N).trans hM
  have hcN : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod N) = 0 := by
    simpa using congrArg (ZMod.castHom hNM (ZMod N)) hγc
  have hcl : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 0 : ℤ) : ZMod l) = 0 := by
    simpa using congrArg (ZMod.castHom hlM (ZMod l)) hγc
  have hdN : (((γ : Matrix (Fin 2) (Fin 2) ℤ) 1 1 : ℤ) : ZMod N) = q := by
    simpa using congrArg (ZMod.castHom hNM (ZMod N)) hγd
  have hδ : sgD N l q * γ⁻¹ ∈ Gam N l := by
    have hS := congrArg (Int.cast : ℤ → ZMod N) (Matrix.SpecialLinearGroup.det_coe (sgD N l q))
    have hG := congrArg (Int.cast : ℤ → ZMod N) (Matrix.SpecialLinearGroup.det_coe γ)
    rw [Matrix.det_fin_two] at hS hG
    push_cast at hS hG
    unfold Gam
    rw [Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_inv, Matrix.adjugate_fin_two]
    simp only [Matrix.mul_apply, Fin.sum_univ_two]
    simp
    push_cast
    generalize (sgD N l q : Matrix (Fin 2) (Fin 2) ℤ) = S at *
    generalize (γ : Matrix (Fin 2) (Fin 2) ℤ) = G at *
    refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
    · linear_combination (↑(S 0 0) : ZMod N) * hdN - (↑(S 0 0) : ZMod N) * hSq + hS
        + (↑(S 0 1) : ZMod N) * hS0N - (↑(S 0 1) : ZMod N) * hcN
    · linear_combination (↑(G 0 0) : ZMod N) * hSq - (↑(G 0 0) : ZMod N) * hdN + hG
        + (↑(G 0 1) : ZMod N) * hcN - (↑(G 0 1) : ZMod N) * hS0N
    · linear_combination (↑(G 1 1) : ZMod N) * hS0N - (↑(S 1 1) : ZMod N) * hcN
    · linear_combination (↑(G 1 1) : ZMod l) * hS0l - (↑(S 1 1) : ZMod l) * hcl
  have hAct : X.act l ↑γ b = X.act l ↑(sgD N l q) b := by
    conv_lhs => rw [← hb' _ hδ]
    rw [Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num)
      (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num), ← Matrix.SpecialLinearGroup.coe_mul,
      inv_mul_cancel_right]
  have hdq : (0 : ℤ) < Matrix.det !![(q : ℤ), 0; 0, 1] := by
    simpa [Matrix.det_fin_two] using hq.pos
  refine ⟨?_, fun s => ?_⟩
  · unfold Tower.heckeT
    simp only [LinearMap.add_apply, LinearMap.sum_apply]
    congr 1
    · symm
      have hinj : ∀ a ∈ Finset.range q, ∀ a' ∈ Finset.range q, a * M % q = a' * M % q → a = a' := by
        intro a ha a' ha' h
        rw [Finset.mem_range] at ha ha'
        have h' : a ≡ a' [MOD q] := Nat.ModEq.cancel_right_of_coprime hqM h
        unfold Nat.ModEq at h'
        rwa [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt ha'] at h'
      refine Finset.sum_nbij (fun j => j * M % q) (fun a _ => Finset.mem_range.mpr (Nat.mod_lt _ hq.pos))
        (fun a ha a' ha' h => hinj a (Finset.mem_coe.mp ha) a' (Finset.mem_coe.mp ha') h) ?_ ?_
      · intro k hk
        obtain ⟨a, ha, h⟩ := Finset.surj_on_of_inj_on_of_card_le (fun a _ => a * M % q)
          (fun a _ => Finset.mem_range.mpr (Nat.mod_lt _ hq.pos)) (fun a a' ha ha' h => hinj a ha a' ha' h)
          le_rfl k (Finset.mem_coe.mp hk)
        exact ⟨a, Finset.mem_coe.mpr ha, h.symm⟩
      · intro a _
        have hdm := Nat.mod_add_div (a * M) q
        generalize a * M % q = r at hdm ⊢
        generalize a * M / q = t at hdm
        let T : SL(2, ℤ) := ⟨!![1, (t : ℤ); 0, 1], by simp [Matrix.det_fin_two]⟩
        have hT : T ∈ Gam N l := by
          unfold Gam
          rw [Subgroup.mem_inf, CongruenceSubgroup.Gamma1_mem, CongruenceSubgroup.Gamma0_mem]
          simp [T]
        have hz : (a : ℤ) * M = r + q * t := by exact_mod_cast hdm.symm
        have hm : !![1, (a : ℤ) * M; 0, (q : ℤ)] = (T : Matrix (Fin 2) (Fin 2) ℤ) * !![1, (r : ℤ); 0, (q : ℤ)] := by
          ext i j
          fin_cases i <;> fin_cases j <;> simp [T, Matrix.mul_apply, Fin.sum_univ_two] <;> linear_combination hz
        rw [hm, ← Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num)
          (by simpa [Matrix.det_fin_two] using hq.pos), hb' T hT]
    · rw [← Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num) hdq,
        ← Tower.act_act Ω ε X l _ _ (by rw [Matrix.SpecialLinearGroup.det_coe]; norm_num) hdq, hAct]
  · unfold Tower.diam
    rw [_root_.GlobalTheory.KZ.GamComm.act_galB_comm ε X N l w hN b hb _ hSmem s, hAct]
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.SInteg
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.HV GlobalTheory.Ord2 GlobalTheory.KZ GlobalTheory.K4 GlobalTheory.KA UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.V.Z.Kato.Nb
open scoped Matrix MatrixGroups Classical

private theorem root_mem {l : ℕ} [hl : Fact l.Prime] (c : Coef l) {x : Qbar l} (hx : x ^ (l - 1) = 1) : x ∈ c.O := by
  have hpos : 0 < l - 1 := Nat.sub_pos_of_lt hl.out.one_lt
  haveI : NeZero (l - 1) := ⟨hpos.ne'⟩
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := (ZMod l)ˣ)
  rw [Nat.card_eq_fintype_card, ZMod.card_units] at hg
  have hg1 : g ∈ rootsOfUnity (l - 1) (ZMod l) := by
    rw [mem_rootsOfUnity, ← hg, pow_orderOf_eq_one]
  rw [← KStar.TotallyRealRoots.map_red_rootsOfUnity (l := l) dvd_rfl] at hg1
  obtain ⟨ζ, hζ, hζg⟩ := hg1
  have hζ1 : ζ ^ (l - 1) = 1 := hζ
  have hp : IsPrimitiveRoot ζ (l - 1) := by
    refine ⟨hζ1, fun k hk => ?_⟩
    rw [← hg, orderOf_dvd_iff_pow_eq_one, ← hζg, ← map_pow, hk, map_one]
  have hinj : Function.Injective (algebraMap ℤ_[l] (Qbar l)) := by
    rw [IsScalarTower.algebraMap_eq ℤ_[l] ℚ_[l] (Qbar l), RingHom.coe_comp]
    exact (algebraMap ℚ_[l] (Qbar l)).injective.comp Subtype.val_injective
  have hq := (IsPrimitiveRoot.coe_units_iff.2 hp).map_of_injective hinj
  obtain ⟨i, -, rfl⟩ := hq.eq_pow_of_pow_eq_one hx
  exact pow_mem (c.O.algebraMap_mem _) i

private theorem nle {l : ℕ} [Fact l.Prime] (c : Coef l) {a : Qbar l} (ha : a ∈ c.O) : ‖a‖ ≤ 1 := by
  have hi : IsIntegral ℤ_[l] a := (Algebra.IsIntegral.isIntegral (R := ℤ_[l]) (⟨a, ha⟩ : c.O)).map c.O.val
  have hq : IsIntegral ℚ_[l] a := Algebra.IsIntegral.isIntegral a
  change spectralValue (minpoly ℚ_[l] a) ≤ 1
  rw [spectralValue_le_one_iff (minpoly.monic hq)]
  intro k
  rw [minpoly.isIntegrallyClosed_eq_field_fractions' ℚ_[l] hi, Polynomial.coeff_map]
  exact PadicInt.norm_le_one _

private theorem mv_mem {l : ℕ} [Fact l.Prime] (c : Coef l) {M : Matrix (Fin 2) (Fin 2) (Qbar l)} {v : Fin 2 → Qbar l}
    (hM : ∀ i k, M i k ∈ c.O) (hv : ∀ k, v k ∈ c.O) (i : Fin 2) : (M *ᵥ v) i ∈ c.O := by
  rw [Matrix.mulVec, dotProduct]
  exact sum_mem fun k _ => mul_mem (hM i k) (hv k)

private def rd (l : ℕ) : (ZMod (l ^ 1))ˣ →* (ZMod l)ˣ :=
  Units.map (ZMod.castHom (dvd_pow_self l one_ne_zero) (ZMod l)).toMonoidHom

private theorem rd_val (l : ℕ) [Fact l.Prime] (y : (ZMod (l ^ 1))ˣ) :
    ((rd l y : (ZMod l)ˣ) : ZMod l) = (((y : ZMod (l ^ 1)).val : ℕ) : ZMod l) := by
  rw [ZMod.natCast_val]; rfl

theorem UpperTheory.V.Z.Kato.Nb.sInteg :
    UpperTheory.V.Z.Kato.Nb.SInteg := by
  intro l hl Ω _ _ _ ι e gN A W ε X pr N _ x c d gm ψ cf hA he hW
  obtain ⟨-, -, -, -, -, -, hpr, -, -, -, -, χ, -, -, hχ⟩ := hA
  have hS := (sSlD Ω ε X N (Nat.pos_of_ne_zero (NeZero.ne N))).2.2.2.2.2.2.2
  have hχ' : ∀ s : G ℚ Ω, (χ s : Qbar l) = ψ (rd l (cycMod ℚ Ω l 1 s) : (ZMod l)ˣ) := fun s => by
    rw [rd_val]; exact hχ s
  have hsurj : ∀ u : (ZMod l)ˣ, ∃ s : G ℚ Ω, rd l (cycMod ℚ Ω l 1 s) = u := by
    intro u
    refine ⟨repM l u, ?_⟩
    have h1 := (sCycZ Ω l 1 (repM l u)).1
    have h2 := (hS (l ^ 1) (repM l u)).2.2.2.2 l (dvd_pow_self l one_ne_zero)
    rw [h1]
    exact h2.trans ((hS l 1).2.2.1 u)
  have h1 : ψ 1 = 1 := by
    have := hχ' 1
    rw [map_one, map_one, map_one, Units.val_one, Units.val_one] at this
    exact this.symm
  have hmul : ∀ u v : (ZMod l)ˣ, ψ ((u * v : (ZMod l)ˣ) : ZMod l) = ψ u * ψ v := by
    intro u v
    obtain ⟨s, rfl⟩ := hsurj u
    obtain ⟨t, rfl⟩ := hsurj v
    rw [← map_mul, ← map_mul, ← hχ', ← hχ', ← hχ', map_mul, Units.val_mul]
  have hpow : ∀ s : G ℚ Ω, χ s ^ (l - 1) = 1 := by
    intro s
    apply Units.ext
    rw [← map_pow, hχ', map_pow, map_pow, ZMod.units_pow_card_sub_one_eq_one, Units.val_one, h1, Units.val_one]
  have hχO : ∀ s : G ℚ Ω, (χ s : Qbar l) ∈ cf.O := fun s =>
    root_mem cf (by rw [← Units.val_pow_eq_pow_val, hpow, Units.val_one])
  have hεO : ∀ s : G ℚ Ω, eps l s ∈ cf.O := fun s => cf.O.algebraMap_mem ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])
  let θ : G ℚ Ω →* (Qbar l)ˣ := (cycBar ℚ Ω l ^ e)⁻¹ * χ
  have hθ : ∀ s, thK l e ψ s = (θ s : Qbar l) := fun s => by
    simp only [thK, θ, ← hχ s, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, Units.val_mul,
      Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val]
  have hθO : ∀ s, (θ s : Qbar l) ∈ cf.O := fun s => by
    have h2 : (θ s : Qbar l) = eps l s⁻¹ ^ e * (χ s : Qbar l) := by
      simp only [θ, eps, map_inv, MonoidHom.mul_apply, MonoidHom.inv_apply, MonoidHom.pow_apply, Units.val_mul,
        Units.val_inv_eq_inv_val, Units.val_pow_eq_pow_val, inv_pow]
    rw [h2]
    exact mul_mem (pow_mem (hεO _) e) (hχO s)
  have hθi : ∀ s, (θ s : Qbar l)⁻¹ = (θ s⁻¹ : (Qbar l)ˣ) := fun s => by
    rw [map_inv, Units.val_inv_eq_inv_val]
  have hρO : ∀ s i k, rhoK W e ψ s i k ∈ cf.O := fun s i k => by
    rw [rhoK, hθ, hθi, Matrix.smul_apply, smul_eq_mul]
    exact mul_mem (hθO _) (hW s i k)
  refine ⟨fun s => ?_, h1, hmul, fun u => ?_, hρO, fun s t => ?_, fun c₀ Y hY r s y i => ?_⟩
  · have h2 := nle cf (hθO s⁻¹)
    rw [← hθi, norm_inv, inv_le_one₀ (norm_pos_iff.2 (θ s).ne_zero)] at h2
    rw [hθ]
    exact le_antisymm (nle cf (hθO s)) h2
  · obtain ⟨s, rfl⟩ := hsurj u
    rw [← hχ']
    exact hχO s
  · simp only [rhoK, hθ, mat, map_mul, Units.val_mul, mul_inv, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    rw [mul_comm ((θ s : Qbar l)⁻¹)]
  · obtain ⟨bB, hbB, b, hb, hc⟩ := hY r 0
    have hF : YfB X l pr W e ψ 0 r N bB s y i ∈ cf.O := by
      unfold YfB GlobalTheory.KA.push
      rw [Finset.sum_apply]
      refine sum_mem fun z _ => mv_mem cf (hρO _) (fun k => hpr _ (hbB _ ?_).1 k) i
      have hM := hS (topM l 0 r (N * N))
      have hm : ∀ s t : Ω ≃ₐ[ℚ] Ω, cycM (topM l 0 r (N * N)) (s * t) = _ := fun s t => (hM s).2.1 t
      have hr := (hM 1).2.2.1
      refine (hM _).2.2.2.1.2 ?_
      have h3 := hm (repM (topM l 0 r (N * N)) z) ((repM (topM l 0 r (N * N)) z)⁻¹ * s *
        repM (topM l 0 r (N * N)) (z * (cycM (topM l 0 r (N * N)) s)⁻¹))
      rw [← mul_assoc, mul_inv_cancel_left, hm, hr, hr, mul_left_comm, mul_inv_cancel, mul_one] at h3
      exact (mul_eq_left.1 h3.symm)
    have h4 := hc s y i
    have h5 := nle cf (add_mem hF (sub_mem (mv_mem cf (hρO s) (hb (y * (cycMod (F := ℚ) (Ω := Ω) l r s)⁻¹)) i) (hb y i)))
    rw [Cg, pow_zero, norm_one] at h4
    have h7 : ∀ a a' : Qbar l, ‖a - a'‖ ≤ 1 → ‖a'‖ ≤ 1 → ‖a‖ ≤ 1 := fun a a' ha ha' => by
      have h6 := (IsUltrametricDist.norm_add_le_max (a - a') a').trans (max_le ha ha')
      rwa [sub_add_cancel] at h6
    exact h7 _ _ h4 h5
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.KatoQuadraticCharacters.EulerFactorBounds.ValCast
section
open scoped MatrixGroups Matrix Classical
open GlobalTheory.KZ GlobalTheory.K4 UpperTheory.V.Z.Kato.Sym UpperTheory.Kd.K4 UpperTheory.V.Z.Kato.Nb

private theorem term {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (l : ℕ) [Fact l.Prime]
    (n N : ℕ) (hN : 0 < N) (s : Ω ≃ₐ[ℚ] Ω) (f : X.Kˣ) (c : ℕ) (k k' : ℤ_[l]) (h : (l : ℤ_[l]) ^ n ∣ k * c - k') :
    AdicCompletion.eval (idl l) (X.Kl l) n (k • clsK X l n (slD X N ((galU X s f ^ c : X.Kˣ) : X.K)) -
      X.kmap l (X.gal s) (k' • clsK X l n (slD X N (f : X.K)))) = 0 := by
  obtain ⟨hRep, -, hPow, hUniq, hMap, -, -⟩ := sCls Ω ε X l n
  obtain ⟨hGalSl, -⟩ := sSlD Ω ε X N hN
  have hApi := (sApi Ω ε X l n).2.2.2.2.1
  have hmul : ∀ a b : X.K, slD X N (a * b) = slD X N a * slD X N b := by
    intro a b
    simp [slD]
  have h1 : slD X N 1 = 1 := by simp [slD]
  have hpow : ∀ (a : X.K) (m : ℕ), slD X N (a ^ m) = slD X N a ^ m := by
    intro a m
    simp [slD]
  let U : X.Kˣ → X.Kˣ := fun u =>
    ⟨slD X N u, slD X N ↑u⁻¹, by rw [← hmul]; simp [h1], by rw [← hmul]; simp [h1]⟩
  have hA := hRep (U (galU X s f ^ c))
  have hB := hPow _ _ c (hMap (X.gal s) _ _ (hRep (U f)))
  have heq : (Units.map (X.gal s : X.K →* X.K) (U f)) ^ c = U (galU X s f ^ c) := by
    ext
    simp only [U, Units.val_pow_eq_pow_val, Units.coe_map, MonoidHom.coe_coe]
    rw [hpow, hGalSl]
    rfl
  rw [heq] at hB
  have hc : Cgr (l ^ n) (U (galU X s f ^ c)) (U (galU X s f ^ c)) := by
    first | rfl | exact ⟨1, by simp⟩ | simp [Cgr]
  have hz := hUniq _ _ _ _ hA hB hc
  rw [map_smul]
  have hsplit : k • clsK X l n (slD X N ((galU X s f ^ c : X.Kˣ) : X.K)) -
      k' • X.kmap l (X.gal s) (clsK X l n (slD X N (f : X.K))) =
      k • (clsK X l n (slD X N ((galU X s f ^ c : X.Kˣ) : X.K)) -
        (c : ℤ_[l]) • X.kmap l (X.gal s) (clsK X l n (slD X N (f : X.K)))) +
      ((k * c) • X.kmap l (X.gal s) (clsK X l n (slD X N (f : X.K))) -
        k' • X.kmap l (X.gal s) (clsK X l n (slD X N (f : X.K)))) := by
    rw [smul_sub, smul_smul]
    abel
  rw [hsplit, map_add (f := _), map_smul, hApi (k * c) k' _ h, add_zero]
  convert smul_zero k using 2

private theorem dvd_iff (l : ℕ) [Fact l.Prime] (n : ℕ) (k k' : ℤ_[l]) :
    (l : ℤ_[l]) ^ n ∣ k - k' ↔ PadicInt.toZModPow n k = PadicInt.toZModPow n k' := by
  rw [← sub_eq_zero, ← map_sub, ← RingHom.mem_ker, PadicInt.ker_toZModPow, Ideal.mem_span_singleton]

private theorem val_cast {M M' : ℕ} [NeZero M] (h : M' ∣ M) (z : ZMod M) :
    ((z.val : ℕ) : ZMod M') = ZMod.castHom h (ZMod M') z := by
  rw [ZMod.castHom_apply, ZMod.cast_eq_val]

private noncomputable def dg {M : ℕ} (d : (ZMod M)ˣ) : GL (Fin 2) (ZMod M) :=
  ⟨!![1, 0; 0, (d : ZMod M)], !![1, 0; 0, ((d⁻¹ : (ZMod M)ˣ) : ZMod M)],
    by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩

theorem UpperTheory.V.Z.Kato.Nb.sXiTw :
    UpperTheory.V.Z.Kato.Nb.SXiTw := by
  intro Ω _ _ _ ε X l _ n N M₀ M w _ _ _ g hL x y P a s
  have hM0 : M₀ ∣ M := hL.eq ▸ Dvd.intro_left N rfl
  have hlM : l ^ n ∣ M := hL.dl.trans hM0
  have hN : 0 < N := Nat.pos_of_ne_zero (NeZero.ne N)
  haveI : NeZero (l ^ n) := ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  obtain ⟨-, -, -, -, -, -, -, hcyc⟩ := sSlD Ω ε X N hN
  have hone : ∀ (K : ℕ) [NeZero K], cycM K (1 : Gal(Ω/ℚ)) = 1 := by
    intro K _
    have h := (hcyc K 1).2.1 1
    rw [mul_one] at h
    exact left_eq_mul.mp h
  have hinv : ∀ (K : ℕ) [NeZero K], cycM K s⁻¹ = (cycM K s)⁻¹ := by
    intro K _
    rw [eq_inv_iff_mul_eq_one, ← (hcyc K s⁻¹).2.1 s, inv_mul_cancel, hone]
  set d := cycM M s with hd
  have hcd : ZMod.castHom hM0 (ZMod M₀) ((d⁻¹ : (ZMod M)ˣ) : ZMod M) = cyc M₀ s⁻¹ := by
    rw [(hcyc M₀ s⁻¹).1, ← ((hcyc M s⁻¹).2.2.2.2 M₀ hM0), hinv M]
    rfl
  have hgr : ∀ (z : Row M₀) (m : GL (Fin 2) (ZMod M)),
      gr M₀ s⁻¹ (z ᵥ* cD N M₀ (m : Matrix (Fin 2) (Fin 2) (ZMod M))) =
        z ᵥ* cD N M₀ ((m * dg d⁻¹ : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) := by
    intro z m
    ext i
    fin_cases i
    · simp [gr, cD, dg, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.mul_apply]
    · simp [gr, cD, dg, Matrix.vecMul, dotProduct, Fin.sum_univ_two, Matrix.mul_apply, val_cast hM0, ← hcd]
      rw [ZMod.cast_mul hM0, ZMod.cast_mul hM0]
      ring
  unfold Xi UpperTheory.Kd.K4.CgF
  intro u
  simp only [Tower.galB, LinearMap.coe_mk, AddHom.coe_mk]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [Finset.sum_filter, Finset.sum_filter, map_sum, map_sub, sub_eq_zero]
  conv_rhs => rw [← Fintype.sum_equiv (Equiv.mulRight (dg d⁻¹)) _ _ (fun _ => rfl)]
  set_option synthInstance.maxHeartbeats 100000 in
    rw [← sub_eq_zero, ← map_sub, ← Finset.sum_sub_distrib, map_sum]
  apply Finset.sum_eq_zero
  intro m _
  simp only [Equiv.coe_mulRight]
  have hdet : Matrix.GeneralLinearGroup.det (m * dg d⁻¹) = Matrix.GeneralLinearGroup.det m * d⁻¹ := by
    rw [map_mul]
    congr 1
    ext
    simp [dg, Matrix.det_fin_two, Matrix.GeneralLinearGroup.val_det_apply]
  have hent : ∀ i, ((m * dg d⁻¹ : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) i 0 =
      (m : Matrix (Fin 2) (Fin 2) (ZMod M)) i 0 ∧
      ((m * dg d⁻¹ : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) i 1 =
      (m : Matrix (Fin 2) (Fin 2) (ZMod M)) i 1 * ((d⁻¹ : (ZMod M)ˣ) : ZMod M) := by
    intro i
    simp [dg, Matrix.mul_apply, Fin.sum_univ_two]
  have hC : Cnd l N g ((m * dg d⁻¹ : GL (Fin 2) (ZMod M)) : Matrix (Fin 2) (Fin 2) (ZMod M)) ↔
      Cnd l N g (m : Matrix (Fin 2) (Fin 2) (ZMod M)) := by
    unfold Cnd
    rw [(hent 1).1, (hent 0).1]
  have hP : Matrix.GeneralLinearGroup.det m * d⁻¹ * d = Matrix.GeneralLinearGroup.det m := by
    rw [mul_assoc, inv_mul_cancel, mul_one]
  simp only [hdet, hP]
  by_cases h : Cnd l N g (m : Matrix (Fin 2) (Fin 2) (ZMod M)) ∧ P (Matrix.GeneralLinearGroup.det m)
  · rw [if_pos h, if_pos ⟨hC.2 h.1, h.2⟩]
    unfold tw
    rw [hgr x m, hgr y m]
    refine term X l n N hN s _ _ _ _ ?_
    rw [dvd_iff]
    simp only [map_sub, map_mul, map_pow, map_add (f := _), map_natCast, (hent 0).1, (hent 0).2]
    have hdl : Units.map (ZMod.castHom hlM (ZMod (l ^ n)) : ZMod M →* ZMod (l ^ n)) d = cycM (l ^ n) s :=
      (hcyc M s).2.2.2.2 (l ^ n) hlM
    have hχ : PadicInt.toZModPow n (((cyclotomicCharacter Ω l) s.toRingEquiv : ℤ_[l]ˣ) : ℤ_[l]) =
        ZMod.castHom hlM (ZMod (l ^ n)) (d : ZMod M) := by
      rw [(dvd_iff l n _ _).1 (sCycZ Ω l n s).2, map_natCast, ZMod.natCast_zmod_val, ← hdl]
      rfl
    have hc : (((cyc (l ^ n) s).val : ℕ) : ZMod (l ^ n)) = ZMod.castHom hlM (ZMod (l ^ n)) (d : ZMod M) := by
      rw [ZMod.natCast_zmod_val, (hcyc (l ^ n) s).1, ← hdl]
      rfl
    simp only [hc, hχ, val_cast hlM, Units.val_mul, mul_inv_rev, inv_inv, map_mul]
    clear hcyc hgr hcd hC hP hdl hone hinv hent hdet h
    set φ := ZMod.castHom hlM (ZMod (l ^ n))
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_fin_one, Matrix.head_cons, map_mul, hχ]
    have hdd : φ ((d⁻¹ : (ZMod M)ˣ) : ZMod M) * φ (d : ZMod M) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have key : φ ((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 1) * φ ((d⁻¹ : (ZMod M)ˣ) : ZMod M) *
        (φ (d : ZMod M) * PadicInt.toZModPow n (u 1)) =
        φ ((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 1) * PadicInt.toZModPow n (u 1) := by
      linear_combination (φ ((m : Matrix (Fin 2) (Fin 2) (ZMod M)) 0 1) * PadicInt.toZModPow n (u 1)) * hdd
    rw [key]
    ring
  · rw [if_neg h, if_neg (fun h' => h ⟨hC.1 h'.1, h'.2⟩), map_zero, sub_zero, map_zero]
end

