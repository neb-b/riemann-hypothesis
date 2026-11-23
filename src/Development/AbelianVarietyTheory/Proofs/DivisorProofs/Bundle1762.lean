module

public import Mathlib
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1646
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StandardLatticeDoubleCosetClassesStabilisers
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FirstStandardPairMemberHasThetaFunction
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1559
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1582
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1632
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FiniteFourierTransformSurjectiveIntegral
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1738
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1634
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1735

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitDetCharacterIntegralFramePowEqOne
section
open NumberField IsDedekindDomain
open scoped Classical Pointwise
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links
open Formalism.MainNotions.TaylorLogMetric (VC embT tor0 lamOf Th La Iop Qbar lamC)
open Formalism.MainNotions.StandardLatticesGL3 (TT stdL pt oddE0 Wd La0 Crv inc OhE IntU)
open GlobalTheory.NormSum (Pair intG)
open GlobalTheory.FunObj.SqNum (hatId CongOne skewLat unitBlock cosetVec)
open GlobalTheory.NormExact (Reads Setup IsFinIdl HasFinPart finPt)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (InId IsUnitDet unitChar stdFst)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.StdRead

noncomputable section

namespace GlobalTheory.StdRead

variable {D : D7}

theorem det_mem_intAf {n : ℕ} {N : Matrix (Fin n) (Fin n) (EAf D)} (h : IsIntM N) :
    N.det ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
  rw [Matrix.det_apply]
  refine sum_mem fun σ _ => ?_
  rw [Units.smul_def]
  exact zsmul_mem (prod_mem fun i _ => h _ _) _

def finHom (D : D7) : AE D →* Formalism.MainNotions.StandardLatticesGL3.AE D :=
  ((GlobalTheory.BotFormula.toAfE D).symm.toRingHom.comp (finPart D)).toMonoidHom

theorem isFinIdl_map (x : (AE D)ˣ) (h : infPart D (x : AE D) = 1) : IsFinIdl x (Units.map (finHom D) x) := by
  refine ⟨h, ?_⟩
  change GlobalTheory.LFun.finAdEquiv D.host.F D.host.E (finPart D (x : AE D)) =
    GlobalTheory.BotFormula.toFinE D ((GlobalTheory.BotFormula.toAfE D).symm (finPart D (x : AE D)))
  rw [← GlobalTheory.BotClassDict.finAdEquiv_toAfE, RingEquiv.apply_symm_apply]

theorem intU_map (x : (AE D)ˣ) (h : toEAf D (x : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h' : toEAf D ((x⁻¹ : (AE D)ˣ) : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    IntU D (Units.map (finHom D) x) := by
  refine ⟨(GlobalTheory.BotClassDict.toAfE_int_iff _).1 ?_, (GlobalTheory.BotClassDict.toAfE_int_iff _).1 ?_⟩
  · change Lev.swapAE D (GlobalTheory.BotFormula.toAfE D ((GlobalTheory.BotFormula.toAfE D).symm (finPart D (x : AE D)))) ∈ _
    rw [RingEquiv.apply_symm_apply]
    exact h
  · change Lev.swapAE D (GlobalTheory.BotFormula.toAfE D ((GlobalTheory.BotFormula.toAfE D).symm (finPart D ((x⁻¹ : (AE D)ˣ) : AE D)))) ∈ _
    rw [RingEquiv.apply_symm_apply]
    exact h'

end GlobalTheory.StdRead

namespace GlobalTheory.StdRead

variable {D : D7}

theorem exists_pow_cong (u : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) (hu : IntU D u) {N : ℕ} (hN : 0 < N) :
    ∃ m : ℕ, 0 < m ∧ ∃ s ∈ OhE D, ((u ^ m : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D) - 1 = (N : Formalism.MainNotions.StandardLatticesGL3.AE D) * s := by
  have hpow : ∀ k : ℕ, ((u : Formalism.MainNotions.StandardLatticesGL3.AE D)) ^ k ∈ OhE D := fun k => pow_mem hu.1 k
  choose b w hw hb using fun k => GlobalTheory.CongApprox.exists_int_approx D N hN _ (hpow k)
  have hI : Ideal.span {((N : ℕ) : 𝓞 D.host.E)} ≠ ⊥ := by
    rw [Ne, Ideal.span_singleton_eq_bot]
    exact_mod_cast hN.ne'
  haveI := Ideal.finiteQuotientOfFreeOfNeBot _ hI
  have key : ∀ i j : ℕ, i < j → Ideal.Quotient.mk (Ideal.span {((N : ℕ) : 𝓞 D.host.E)}) (b i) =
      Ideal.Quotient.mk (Ideal.span {((N : ℕ) : 𝓞 D.host.E)}) (b j) →
      ∃ m : ℕ, 0 < m ∧ ∃ s ∈ OhE D,
        ((u ^ m : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D) - 1 = (N : Formalism.MainNotions.StandardLatticesGL3.AE D) * s := by
    intro i j hij hq
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 (Ideal.Quotient.eq.1 hq.symm)
    have ht' : inc D ((b j : 𝓞 D.host.E) : D.host.E) - inc D ((b i : 𝓞 D.host.E) : D.host.E) =
        (N : Formalism.MainNotions.StandardLatticesGL3.AE D) * inc D ((t : 𝓞 D.host.E) : D.host.E) := by
      have := congrArg (fun z : 𝓞 D.host.E => inc D (z : D.host.E)) ht
      simp only [map_mul, map_sub, map_natCast] at this
      rw [← this, mul_comm]
    set U := (u : Formalism.MainNotions.StandardLatticesGL3.AE D)
    set V := ((u⁻¹ : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D)
    have hUV : U * V = 1 := Units.mul_inv u
    refine ⟨j - i, Nat.sub_pos_of_lt hij, (inc D ((t : 𝓞 D.host.E) : D.host.E) + w j - w i) * V ^ i,
      mul_mem (sub_mem (add_mem (GlobalTheory.CongApprox.inc_mem_OhE D t) (hw j)) (hw i)) (pow_mem hu.2 i), ?_⟩
    have hj : U ^ j = U ^ (j - i) * U ^ i := by rw [← pow_add, Nat.sub_add_cancel hij.le]
    have e1 : U ^ j - U ^ i = (N : Formalism.MainNotions.StandardLatticesGL3.AE D) * (inc D ((t : 𝓞 D.host.E) : D.host.E) + w j - w i) := by
      rw [hb j, hb i]
      linear_combination ht'
    rw [Units.val_pow_eq_pow_val]
    calc U ^ (j - i) - 1 = (U ^ j - U ^ i) * V ^ i := by
          rw [hj, sub_mul, mul_assoc, ← mul_pow, hUV, one_pow, mul_one]
      _ = _ := by rw [e1, mul_assoc]
  obtain ⟨i, j, hij, hq⟩ := Finite.exists_ne_map_eq_of_infinite
    (fun k : ℕ => Ideal.Quotient.mk (Ideal.span {((N : ℕ) : 𝓞 D.host.E)}) (b k))
  rcases lt_or_gt_of_ne hij with h | h
  · exact key i j h hq
  · exact key j i h hq.symm

theorem absNorm_mem_conj (𝔪 : Ideal (𝓞 D.host.E)) : ((Ideal.absNorm 𝔪 : ℕ) : 𝓞 D.host.E) ∈ D.host.conj • 𝔪 := by
  have := Ideal.smul_mem_pointwise_smul D.host.conj _ 𝔪 (Ideal.absNorm_mem 𝔪)
  have h2 : D.host.conj • ((Ideal.absNorm 𝔪 : ℕ) : 𝓞 D.host.E) = ((Ideal.absNorm 𝔪 : ℕ) : 𝓞 D.host.E) := by
    first
    | exact smul_natCast _ _
    | simp
    | exact map_natCast (MulSemiringAction.toRingHom _ _ D.host.conj) _
  rw [h2] at this
  exact this

end GlobalTheory.StdRead

namespace GlobalTheory.StdRead

variable {D : D7}

theorem unitChar_pow_eq_one : ∀ {D : D7} (e : AE D) (𝔪 : Ideal (𝓞 D.host.E)), GoodMod e 𝔪 → ∀ ν : (AE D)ˣ →* Circle,
    KillsCong ν 𝔪 → ∀ {n : ℕ} (β : GL (Fin n) (EAf D)), IsIntM β.val → IsIntM (β⁻¹).val →
    ∃ m : ℕ, 0 < m ∧ unitChar ν e β.val ^ m = 1 := by
  intro D e 𝔪 h𝔪 ν hν n β hβ hβ'
  have h0 := h𝔪.ne_bot
  obtain ⟨SS, c, he, -, -, -⟩ := h𝔪
  have hE := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.toEAf_mem he
  have hee : toEAf D e * toEAf D e = toEAf D e := by rw [← map_mul, GlobalTheory.PlaceDatum.idemSum_mul_self he]
  have hd := det_mem_intAf hβ
  have hd' := det_mem_intAf hβ'
  have hdd : β.val.det * (β⁻¹).val.det = 1 := by rw [← Matrix.det_mul, Units.mul_inv, Matrix.det_one]
  have huv : (1 - toEAf D e + toEAf D e * β.val.det) * (1 - toEAf D e + toEAf D e * (β⁻¹).val.det) = 1 := by
    linear_combination (1 - β.val.det - (β⁻¹).val.det + β.val.det * (β⁻¹).val.det) * hee + toEAf D e * hdd
  obtain ⟨x, a1, a2, a3⟩ := StandardFirstTheta.GlobalTheory.CompanionTheory.StdFstTheta.exists_unit huv
  have hex : ∃ x, IsUnitDet e β.val x :=
    ⟨x, a1, a2, by rw [a3]; exact add_mem (sub_mem (one_mem _) hE) (mul_mem hE hd')⟩
  obtain ⟨h1, h2, h3⟩ := hex.choose_spec
  set x0 := hex.choose
  have hx0 : toEAf D (x0 : AE D) ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := by
    rw [h2]
    exact add_mem (sub_mem (one_mem _) hE) (mul_mem hE hd)
  have hN : 0 < Ideal.absNorm 𝔪 * Ideal.absNorm 𝔪 :=
    Nat.mul_pos (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h0)) (Nat.pos_of_ne_zero (Ideal.absNorm_eq_zero_iff.not.2 h0))
  obtain ⟨m, hm, s, hs, hys⟩ := exists_pow_cong (Units.map (finHom D) x0) (intU_map x0 hx0 h3) hN
  have hinf : infPart D ((x0 ^ m : (AE D)ˣ) : AE D) = 1 := by
    rw [Units.val_pow_eq_pow_val, map_pow, h1, one_pow]
  have hfin : IsFinIdl (x0 ^ m) ((Units.map (finHom D) x0) ^ m) := by
    rw [← map_pow]
    exact isFinIdl_map _ hinf
  have hU : IntU D ((Units.map (finHom D) x0) ^ m) := by
    have hu := intU_map x0 hx0 h3
    refine ⟨?_, ?_⟩
    · rw [Units.val_pow_eq_pow_val]
      exact pow_mem hu.1 m
    · rw [← inv_pow, Units.val_pow_eq_pow_val]
      exact pow_mem hu.2 m
  have hmem : (((Units.map (finHom D) x0) ^ m : (Formalism.MainNotions.StandardLatticesGL3.AE D)ˣ) : Formalism.MainNotions.StandardLatticesGL3.AE D) - 1 ∈
      hatId D (𝔪 * D.host.conj • 𝔪) := by
    rw [hys]
    refine AddSubgroup.subset_closure ⟨((Ideal.absNorm 𝔪 * Ideal.absNorm 𝔪 : ℕ) : 𝓞 D.host.E), ?_, s, hs, ?_⟩
    · rw [Nat.cast_mul]
      exact Ideal.mul_mem_mul (Ideal.absNorm_mem 𝔪) (absNorm_mem_conj 𝔪)
    · simp only [map_natCast]
  have hk : ν (x0 ^ m) = 1 := hν _ _ hfin hU hmem
  have hc : ((ν x0)⁻¹ : Circle) ^ m = 1 := by rw [inv_pow, ← map_pow, hk, inv_one]
  refine ⟨m, hm, ?_⟩
  unfold unitChar
  rw [dite_eq_left hex]
  have := congrArg (fun z : Circle => (z : ℂ)) hc
  simpa using this

end GlobalTheory.StdRead
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForWeylElement
section
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.WeylFour
open scoped GlobalTheory.VacAny


open GlobalTheory.SympChange in
theorem GlobalTheory.WeylFour.weyl_hasOp : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    (∀ᶠ v in cofinite, PsiUnr ψ v) → (∀ v : Pl (F := F), ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ] [DecidableEq κ],
    GlobalTheory.SympChange.HasOp ψ (GlobalTheory.SympChange.weylM (F := F) (κ := κ)) := by
  intro F _ _ ψ hψ hunr hnt κ _ _
  classical

  have hsp : ∀ {R : Type} [CommRing R] [Algebra F R] (w : (κ → R) × (κ → R)),
      spAct (weylM (F := F) (κ := κ)) w = (w.2, -w.1) := by
    intro R _ _ w
    ext k
    · simp [spAct, weylM, Matrix.fromBlocks_map, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Matrix.one_apply]
    · simp [spAct, weylM, Matrix.fromBlocks_map, Matrix.mulVec, dotProduct, Matrix.fromBlocks, Matrix.one_apply]

  have hSB := fun v => GlobalTheory.T.local_fourier_schwartz_stable F ψ hψ v (hnt v) κ
  have hInv := fun v => GlobalTheory.T.local_fourier_double_reflection F ψ hψ v (hnt v) κ
  have hLaw := GlobalTheory.T.local_fourier_schrodinger_intertwine F ψ hψ
  have hInd := fun v => GlobalTheory.T.local_lattice_indicator_fourier F ψ hψ v κ
  have hsmV : ∀ v (c : ℂ) (φ : (κ → Fv F v) → ℂ), fourV ψ v (c • φ) = c • fourV ψ v φ := by
    intro v c φ; funext y
    simp only [fourV, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _
  have h0V : ∀ v, fourV ψ v (0 : (κ → Fv F v) → ℂ) = 0 := by
    intro v; funext y; simp [fourV]
  choose C hC using fun v : Pl F => Submodule.exists_isCompl (SB (κ → Fv F v))
  let P : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ) := fun v =>
    (SB (κ → Fv F v)).subtype ∘ₗ Submodule.linearProjOfIsCompl _ (C v) (hC v)
  have hPmem : ∀ v φ, P v φ ∈ SB (κ → Fv F v) := fun v φ => (Submodule.linearProjOfIsCompl _ (C v) (hC v) φ).2
  have hPid : ∀ v, ∀ φ ∈ SB (κ → Fv F v), P v φ = φ := fun v φ hφ =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left (hC v) ⟨φ, hφ⟩)
  let ev : ∀ v : Pl (F := F), ((κ → Fv F v) → ℂ) →ₗ[ℂ] ((κ → Fv F v) → ℂ) := fun v =>
    { toFun := fun φ => fourV ψ v (P v φ)
      map_add' := fun φ χ => by
        rw [map_add (f := _)]; exact (hSB v).2.1 _ (hPmem v φ) _ (hPmem v χ)
      map_smul' := fun c φ => by
        rw [map_smul, RingHom.id_apply]; exact hsmV v c _ }
  have hev : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ = fourV ψ v φ := fun v φ hφ => by
    show fourV ψ v (P v φ) = _
    rw [hPid v φ hφ]
  have hneg : ∀ v, ∀ φ ∈ SB (κ → Fv F v), (fun x => φ (-x)) ∈ SB (κ → Fv F v) := fun v φ hφ =>
    ⟨hφ.1.comp_continuous continuous_neg, hφ.2.comp_homeomorph (Homeomorph.neg _)⟩
  have hmap : ∀ v, (SB (κ → Fv F v)).map (ev v) = SB _ := by
    intro v
    apply le_antisymm
    · rintro _ ⟨φ, hφ, rfl⟩
      rw [hev v φ hφ]; exact (hSB v).1 φ hφ
    · intro φ hφ
      have h1 := hneg v φ hφ
      refine ⟨fourV ψ v (fun x => φ (-x)), (hSB v).1 _ h1, ?_⟩
      rw [hev v _ ((hSB v).1 _ h1), hInv v _ h1]
      simp
  have hinj : ∀ v, ∀ φ ∈ SB (κ → Fv F v), ev v φ = 0 → φ = 0 := by
    intro v φ hφ h
    rw [hev v φ hφ] at h
    have h2 := hInv v φ hφ
    rw [h, h0V] at h2
    funext x
    have h3 := congrFun h2 (-x)
    simp only [Pi.zero_apply, neg_neg] at h3
    exact h3.symm

  obtain ⟨ei, hsurj, hei, hcont⟩ := _root_.GlobalTheory.WeylFour.exists_fourier_measI F κ
  obtain ⟨μ, hμ, hprod⟩ := GlobalTheory.T.exists_haar_adelic_integral_formula F ψ hψ hunr hnt κ
  haveI := hμ
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  have hspan := GlobalTheory.T.schwartz_adelic_eq_span_pure F κ
  let fA : ((κ → AF F) → ℂ) → (κ → AF F) → ℂ := fun Φ y => ∫ x, Φ x * ψ (x ⬝ᵥ y) ∂μ
  have hpure : ∀ (f : SInf F κ) (φ : ∀ v : Pl (F := F), (κ → Fv F v) → ℂ), (∀ v, φ v ∈ SB _) →
      (∀ᶠ v in cofinite, φ v = indO v) → ∀ y, Integrable (fun x => pure f φ x * ψ (x ⬝ᵥ y)) μ ∧
        fA (pure f φ) y = pure (ei f) (fun v => fourV ψ v (φ v)) y := by
    intro f φ hφ hae y
    obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.schwartz_bruhat_restricted_product_char F ψ hψ hunr κ f φ y hφ hae
    have e : (fun x => pure f φ x * ψ (x ⬝ᵥ y)) = fun x =>
        (fun z => f z * eInf z (fun i => evI F (y i))) (fun i => evI F (x i)) *
          ∏ᶠ v, (fun z => φ v z * GlobalTheory.LatVac.psiAt ψ v (z ⬝ᵥ fun i => evFin F v (y i))) (fun i => evFin F v (x i)) :=
      funext h3
    obtain ⟨hc, hi⟩ := hcont f (fun i => evI F (y i))
    obtain ⟨j1, j2⟩ := hprod _ _ hc hi h1 h2
    refine ⟨e ▸ j1, ?_⟩
    show (∫ x, pure f φ x * ψ (x ⬝ᵥ y) ∂μ) = _
    rw [e, j2, ← hei]
    rfl
  have hint : ∀ Φ ∈ schA F κ, ∀ y, Integrable (fun x => Φ x * ψ (x ⬝ᵥ y)) μ := by
    intro Φ hΦ y
    rw [hspan] at hΦ
    induction hΦ using Submodule.span_induction with
    | mem Φ h =>
      obtain ⟨f, φ, hφ, hae, rfl⟩ := h
      exact (hpure f φ hφ hae y).1
    | zero => simp
    | add Φ Ψ _ _ h1 h2 =>
      refine (h1.add h2).congr (Filter.Eventually.of_forall fun x => ?_)
      simp [add_mul]
    | smul c Φ _ h => simpa [mul_assoc] using h.const_mul c
  have hadd : ∀ Φ ∈ schA F κ, ∀ Ψ ∈ schA F κ, fA (Φ + Ψ) = fA Φ + fA Ψ := by
    intro Φ hΦ Ψ hΨ; funext y
    simp only [fA, Pi.add_apply, add_mul]
    exact integral_add (hint Φ hΦ y) (hint Ψ hΨ y)
  have hsmul : ∀ (c : ℂ) (Φ : (κ → AF F) → ℂ), fA (c • Φ) = c • fA Φ := by
    intro c Φ; funext y
    simp only [fA, Pi.smul_apply, smul_eq_mul, mul_assoc]
    exact integral_const_mul c _
  have hkeep : ∀ Φ ∈ schA F κ, fA Φ ∈ schA F κ := by
    intro Φ hΦ
    rw [hspan] at hΦ ⊢
    induction hΦ using Submodule.span_induction with
    | mem Φ h =>
      obtain ⟨f, φ, hφ, hae, rfl⟩ := h
      have e : fA (pure f φ) = pure (ei f) (fun v => fourV ψ v (φ v)) := funext fun y => (hpure f φ hφ hae y).2
      rw [e]
      refine Submodule.subset_span ⟨ei f, fun v => fourV ψ v (φ v), fun v => (hSB v).1 _ (hφ v), ?_, rfl⟩
      filter_upwards [hae, hunr] with v h1 h2
      rw [h1, (hInd v).2 h2]
    | zero =>
      have : fA 0 = 0 := by funext y; simp [fA]
      rw [this]; exact zero_mem _
    | add Φ Ψ hΦ hΨ h1 h2 =>
      rw [hadd Φ (hspan ▸ hΦ) Ψ (hspan ▸ hΨ)]; exact add_mem h1 h2
    | smul c Φ _ h =>
      rw [hsmul]; exact Submodule.smul_mem _ c h
  have hlawA : ∀ w Φ, fA (schr ψ w Φ) = schr ψ (w.2, -w.1) (fA Φ) := by
    intro w Φ; funext y
    simp only [fA, schr]
    have h1 := integral_add_right_eq_self (μ := μ) (fun z => ψ ((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) *
      Φ z * ψ ((z - w.1) ⬝ᵥ y)) w.1
    simp only [add_sub_cancel_right] at h1
    rw [h1, ← integral_const_mul]
    congr 1; funext z
    have h2 : (⅟(2 : AF F)) + ⅟2 = 1 := invOf_two_add_invOf_two
    have key : ((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) + (z - w.1) ⬝ᵥ y =
        (y ⬝ᵥ -w.1 + ⅟2 * (w.2 ⬝ᵥ -w.1)) + z ⬝ᵥ (y + w.2) := by
      simp only [sub_dotProduct, dotProduct_add, dotProduct_neg]
      rw [dotProduct_comm w.2 w.1, dotProduct_comm y w.1]
      linear_combination (w.1 ⬝ᵥ w.2) * h2
    calc ψ ((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) * Φ z * ψ ((z - w.1) ⬝ᵥ y)
        = Φ z * ψ (((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) + (z - w.1) ⬝ᵥ y) := by
          rw [AddChar.map_add_eq_mul ψ ((z - w.1) ⬝ᵥ w.2 + ⅟(2 : AF F) * (w.1 ⬝ᵥ w.2)) ((z - w.1) ⬝ᵥ y)]; ring
      _ = _ := by
          rw [key, AddChar.map_add_eq_mul ψ (y ⬝ᵥ -w.1 + ⅟2 * (w.2 ⬝ᵥ -w.1)) (z ⬝ᵥ (y + w.2))]; ring
  obtain ⟨D, hD⟩ := Submodule.exists_isCompl (schA F κ)
  let Q : ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) := (schA F κ).subtype ∘ₗ Submodule.linearProjOfIsCompl _ D hD
  have hQmem : ∀ Φ, Q Φ ∈ schA F κ := fun Φ => (Submodule.linearProjOfIsCompl _ D hD Φ).2
  have hQid : ∀ Φ ∈ schA F κ, Q Φ = Φ := fun Φ hΦ =>
    congrArg Subtype.val (Submodule.linearProjOfIsCompl_apply_left hD ⟨Φ, hΦ⟩)
  let e : ((κ → AF F) → ℂ) →ₗ[ℂ] (κ → AF F) → ℂ :=
    { toFun := fun Φ => fA (Q Φ)
      map_add' := fun Φ Ψ => by rw [map_add (f := _)]; exact hadd _ (hQmem Φ) _ (hQmem Ψ)
      map_smul' := fun c Φ => by rw [map_smul, RingHom.id_apply]; exact hsmul c _ }
  have he : ∀ Φ ∈ schA F κ, e Φ = fA Φ := fun Φ hΦ => by
    show fA (Q Φ) = _
    rw [hQid Φ hΦ]
  refine ⟨e, ei, ev, hsurj, fun Φ hΦ => ?_, fun w Φ hΦ => ?_, hmap, hinj, fun v w φ hφ => ?_, ?_, ?_⟩
  · rw [he Φ hΦ]; exact hkeep Φ hΦ
  · rw [he _ (_root_.GlobalTheory.WeylFour.SchrKeep.schr_mem_schA F ψ hψ κ w Φ hΦ), he Φ hΦ, hlawA, hsp]
  · rw [hsp, hev v _ ((hSB v).2.2 w φ hφ), hev v φ hφ, hLaw v κ w φ]
  · filter_upwards [hunr] with v hv
    rw [hev v _ (hInd v).1, (hInd v).2 hv]
  · intro f φ hφ hae
    have hm : pure f φ ∈ schA F κ := by
      rw [hspan]; exact Submodule.subset_span ⟨f, φ, hφ, hae, rfl⟩
    have e2 : (fun v => ev v (φ v)) = fun v => fourV ψ v (φ v) := funext fun v => hev v _ (hφ v)
    rw [he _ hm, e2]
    exact funext fun y => (hpure f φ hφ hae y).2
end

