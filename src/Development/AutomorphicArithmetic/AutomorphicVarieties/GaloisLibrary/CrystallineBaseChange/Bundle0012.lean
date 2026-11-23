module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0005
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0009
public import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.CurveDVRSpecialization.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.SelfDualR
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.AlgOfCyc
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.Bundle0010
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.Bundle0007
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0124
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0008
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0007
public import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Bundle0011
public import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.NewformCoefficients.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.Bundle0063

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.CharpolySmul
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.GalOfCusp Formalism.WeaklyAdmissibleFiltrations
open scoped Matrix

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere

open UpperTheory.V UpperTheory.V.Af

private theorem flag_stable {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) (D N N' : Subgroup Γ) (hN : N ≤ N')
    (hc : ∀ d ∈ D, ∀ s ∈ N, d⁻¹ * s * d ∈ N) (χ : Fin 2 → Γ →* kˣ) (hne : ∃ s ∈ N, χ 0 s ≠ χ 1 s)
    (h : IsFlagOn r N' fun i => (χ i).comp N'.subtype) :
    ∃ κ, IsFlagOn r D κ ∧ ∀ i (s : ↥D), (s : Γ) ∈ N → κ i s = χ i s := by
  obtain ⟨g, hg⟩ := h
  obtain ⟨s0, hs0, hne⟩ := hne
  let M : Γ →* GL (Fin 2) k := (MulAut.conj g).toMonoidHom.comp r
  have hM : ∀ s, M s = g * r s * g⁻¹ := fun _ => rfl
  have h1 : ∀ s ∈ N, M s 1 0 = 0 := fun s hs => (hg ⟨s, hN hs⟩).1 1 0 (by decide)
  have h2 : ∀ s ∈ N, ∀ i, M s i i = χ i s := fun s hs i => (hg ⟨s, hN hs⟩).2 i
  have hmul : ∀ s t i j, M (s * t) i j = M s i 0 * M t 0 j + M s i 1 * M t 1 j := fun s t i j => by
    rw [map_mul, Units.val_mul, Matrix.mul_apply, Fin.sum_univ_two]
  have h3 : ∀ d ∈ D, M d 1 0 = 0 := fun d hd => by
    have e : s0 * d = d * (d⁻¹ * s0 * d) := by group
    have e2 := hmul s0 d 1 0
    have e3 : χ 0 (d⁻¹ * s0 * d) = χ 0 s0 := by rw [map_mul, map_mul, map_inv, mul_right_comm]; simp
    rw [e, hmul, h1 _ (hc d hd s0 hs0), h1 _ hs0, h2 _ (hc d hd s0 hs0), h2 _ hs0, e3] at e2
    have : (χ 0 s0 : k) - χ 1 s0 ≠ 0 := sub_ne_zero.2 fun h => hne (Units.ext h)
    apply mul_left_cancel₀ this
    linear_combination e2
  refine ⟨fun i => MonoidHom.toHomUnits
    { toFun := fun s => M s i i
      map_one' := by simp
      map_mul' := fun s t => by
        rw [Subgroup.coe_mul, hmul]
        fin_cases i
        · simp [h3 _ t.2]
        · simp [h3 _ s.2] }, ⟨g, fun s => ⟨fun i j hij => ?_, fun i => rfl⟩⟩, fun i s hs => Units.ext (h2 _ hs i)⟩
  fin_cases i <;> fin_cases j
  · exact absurd hij (by decide)
  · exact absurd hij (by decide)
  · exact h3 _ s.2
  · exact absurd hij (by decide)

private theorem dual_det {Γ k : Type} [Group Γ] [Field k] (r : Γ →* GL (Fin 2) k) :
    DualTw r (Matrix.GeneralLinearGroup.det.comp r) := by
  refine ⟨⟨!![0, 1; -1, 0], !![0, -1; 1, 0], by simp [Matrix.one_fin_two], by simp [Matrix.one_fin_two]⟩, fun s => ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.det_fin_two] <;> ring

private theorem ss_tw {Γ k : Type} [Group Γ] [Field k] {n : ℕ} (r : Γ →* GL (Fin n) k) (χ : Γ →* kˣ)
    (h : IsSSRep r) : IsSSRep (tw r χ) := by
  have hinv (W : Submodule k (Fin n → k)) : IsInv (tw r χ) W ↔ IsInv r W := by
    constructor
    · intro hW g v hv
      have hsmul := W.smul_mem ((χ g : k)⁻¹) (hW g v hv)
      rwa [tw_val, Matrix.smul_mulVec, smul_smul, inv_mul_cancel₀ (Units.ne_zero _), one_smul] at hsmul
    · intro hW g v hv
      rw [tw_val, Matrix.smul_mulVec]
      exact W.smul_mem _ (hW g v hv)
  intro W hW
  obtain ⟨W', hW', hcompl⟩ := h W ((hinv W).1 hW)
  exact ⟨W', (hinv W').2 hW', hcompl⟩

private theorem place_of {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {p : ℕ} [hp : Fact p.Prime]
    {A : ValuationSubring Ω} (hA : A.valuation (p : Ω) < 1) {w : HeightOneSpectrum (𝓞 ℚ)} (hw : (p : 𝓞 ℚ) ∈ w.asIdeal) :
    IsPlaceOver A w := by
  obtain ⟨p1, p2, p3, -⟩ := UpperTheory.V.Base.places ℚ Ω p A
  obtain ⟨v, hv⟩ := p1 fun h => (p2 h).2 hA
  have hpr : Prime (p : 𝓞 ℚ) := by
    have e : (p : 𝓞 ℚ) = Rat.ringOfIntegersEquiv.symm (p : ℤ) := by simp
    rw [e]
    exact (MulEquiv.prime_iff Rat.ringOfIntegersEquiv.symm.toMulEquiv).mpr (Nat.prime_iff_prime_int.1 hp.out)
  have hm : (Ideal.span {(p : 𝓞 ℚ)}).IsMaximal :=
    ((Ideal.span_singleton_prime hpr.ne_zero).2 hpr).isMaximal (by rw [Ne, Ideal.span_singleton_eq_bot]; exact hpr.ne_zero)
  have e : v = w := HeightOneSpectrum.ext
    ((hm.eq_of_le v.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 ((p3 v hv).1 hA))).symm.trans
      (hm.eq_of_le w.isPrime.ne_top ((Ideal.span_singleton_le_iff_mem _).2 hw)))
  exact e ▸ hv

private theorem cont_cycBar (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] (l : ℕ) [Fact l.Prime] :
    Continuous (cycBar F Ω l) :=
  (Continuous.units_map ((algebraMap ℚ_[l] (Qbar l)).comp PadicInt.Coe.ringHom).toMonoidHom
    ((continuous_algebraMap ℚ_[l] (Qbar l)).comp continuous_subtype_val)).comp (continuous_cycZ F Ω l)

private theorem cyc_inf {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [hl : Fact l.Prime]
    {A : ValuationSubring Ω} (hA : A.valuation (l : Ω) < 1) :
    ∃ s ∈ Ine (F := ℚ) A, ∀ k : ℕ, k ≠ 0 → cycBar ℚ Ω l s ^ k ≠ 1 := by
  have hu : IsUnit ((l + 1 : ℕ) : ℤ_[l]) := by
    rw [PadicInt.isUnit_iff]
    exact PadicInt.norm_natCast_eq_one_iff.2 (by simp)
  obtain ⟨s, hs, he⟩ := GlobalTheory.CycInertia.cycZ_Ine_surjective Ω l A hA hu.unit
  refine ⟨s, hs, fun k hk h => ?_⟩
  have h2 : ((cycBar ℚ Ω l s : (Qbar l)ˣ) : Qbar l) = (l + 1 : ℕ) := by
    change algebraMap ℚ_[l] (Qbar l) (PadicInt.Coe.ringHom ((cycZ ℚ Ω l s : ℤ_[l]ˣ) : ℤ_[l])) = _
    rw [he, hu.unit_spec, map_natCast, map_natCast]
  have h3 := congrArg Units.val h
  rw [Units.val_pow_eq_pow_val, h2, Units.val_one, ← Nat.cast_pow, Nat.cast_eq_one, Nat.pow_eq_one] at h3
  have := hl.out.pos
  omega

private theorem charpoly_smul {k : Type} [Field k] (φ : k →+* ℂ) (M : Matrix (Fin 2) (Fin 2) k) (c : k) (hc : c ≠ 0)
    (B : Multiset ℂ) (h : M.charpoly.map φ = (B.map fun b => X - C b).prod) :
    (c • M).charpoly.map φ = (B.map fun b => X - C (φ c * b)).prod := by
  have hcard : B.card = 2 := by
    simpa only [natDegree_map, Matrix.charpoly_natDegree_eq_dim, Fintype.card_fin,
      natDegree_multiset_prod_X_sub_C_eq_card] using (congrArg natDegree h).symm
  obtain ⟨x, y, rfl⟩ := Multiset.card_eq_two.1 hcard
  rw [Matrix.charpoly_fin_two] at h ⊢
  simp only [Multiset.insert_eq_cons, Multiset.map_cons, Multiset.map_singleton, Multiset.prod_cons,
    Multiset.prod_singleton, Polynomial.map_add, Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_pow,
    map_X, map_C, Matrix.trace_smul, Matrix.det_smul, smul_eq_mul, map_mul, map_pow, Fintype.card_fin] at h ⊢
  have hzero := congrArg (eval 0) h
  have hone := congrArg (eval 1) h
  simp only [eval_add, eval_sub, eval_mul, eval_pow, eval_X, eval_C] at hzero hone
  have hdet : φ M.det = x * y := by linear_combination hzero
  have htrace : φ M.trace = x + y := by linear_combination hzero - hone
  rw [hdet, htrace]
  simp only [C_mul, C_add]
  ring

end UpperTheory.V.Br.AutomorphicNewformFromAlmostEverywhere
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.Deadel
section
noncomputable section

open NumberField Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual
open GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Af.Nf UpperTheory.V.Sd CongruenceSubgroup
open UpperHalfPlane hiding I
open scoped Matrix MatrixGroups ModularForm

namespace UpperTheory.V.Br

private theorem nsl_aff (k : ℕ) (f : ℍ → ℂ) (z : ℍ) :
    nsl k f (aff (Units.mk0 z.im z.im_pos.ne') z.re : GL (Fin 2) ℝ) UpperHalfPlane.I =
      ((z.im ^ ((k : ℝ) / 2) : ℝ) : ℂ) * f z := by
  have hd : (aff (Units.mk0 z.im z.im_pos.ne') z.re : GL (Fin 2) ℝ).val.det = z.im := by simp [aff, Matrix.det_fin_two]
  have hz : (z.im : ℂ) * Complex.I + z.re = z := by
    rw [add_comm]; exact Complex.re_add_im (z : ℂ)
  rw [nsl, hd, abs_of_pos z.im_pos, sign_pos z.im_pos]
  simp [aff, hz]

private theorem isLow_fin {k : ℕ} {φ : TR.Sm ℚ 2} (h : IsLow k φ) (u : GL (Fin 2) (Af ℚ)) : IsLow k (TR.finRep ℚ 2 u φ) := by
  have e : ∀ v i j, TR.Eop v i j (TR.finRep ℚ 2 u φ) = TR.finRep ℚ 2 u (TR.Eop v i j φ) := fun v i j =>
    LinearMap.congr_fun (TR.lie_rt_fin _ u) φ
  refine ⟨fun v => ?_, fun v => ?_, fun v => ?_⟩
  · rw [e, e, ← map_sub, h.wt, map_smul]
  · rw [e, e, e, e, ← map_sub, h.low, map_smul, map_add (f := _)]
  · rw [e, e, ← map_add (f := _), h.one, map_zero]

private theorem cusp_fin {φ : TR.Sm ℚ 2} (h : TR.IsCuspForm φ) (u : GL (Fin 2) (Af ℚ)) : TR.IsCuspForm (TR.finRep ℚ 2 u φ) := by
  refine ⟨(UpperTheory.hecke_operators_commute_on_automorphic_forms ℚ 2).2.1 φ u h.1, fun r h0 h1 _ _ μ 𝓕 hμ hF g => ?_⟩
  have e : ∀ x : BlockIx 2 r → Ad ℚ, (TR.finRep ℚ 2 u φ).1 (unip x * g) = φ.1 (unip x * (g * finGL ℚ 2 u)) := fun x =>
    congrArg φ.1 (mul_assoc _ _ _)
  simp only [e]
  exact h.2 r h0 h1 μ 𝓕 hμ hF _

private theorem down_fin {k N : ℕ} {f : ℍ → ℂ} {φ : TR.Sm ℚ 2} (hl : ∀ γ g, φ.1 (ratGL ℚ 2 γ * g) = φ.1 g)
    (h : Nf.IsLift k N f φ.1) (γ : SL(2, ℤ)) :
    down k (TR.finRep ℚ 2 (toF (Matrix.SpecialLinearGroup.mapGL ℚ γ))⁻¹ φ).1 = f ∣[(k : ℤ)] γ := by
  funext z
  set δ : GL (Fin 2) ℚ := Matrix.SpecialLinearGroup.mapGL ℚ γ with hδ
  set x : GL (Fin 2) ℝ := aff (Units.mk0 z.im z.im_pos.ne') z.re with hx
  have hv : (toR δ).val = γ.1.map (Int.cast : ℤ → ℝ) := by
    ext a b
    change Rat.castHom ℝ (algebraMap ℤ ℚ (γ a b)) = _
    simp
  have hd : 0 < x.val.det := by simp [hx, aff, Matrix.det_fin_two, z.im_pos]
  have e : ratGL ℚ 2 δ * (upR x * finGL ℚ 2 (toF δ)⁻¹) = ratGL ℚ 2 1 * (upR (toR δ * x) * finGL ℚ 2 1) := by
    rw [ratGL_eq, upR_comm x, mul_assoc, ← mul_assoc (finGL ℚ 2 (toF δ)), ← map_mul, mul_inv_cancel]
    simp
  change ((z.im ^ (-((k : ℝ) / 2)) : ℝ) : ℂ) * φ.1 (upR x * finGL ℚ 2 (toF δ)⁻¹) = _
  rw [← hl δ, e, h 1 _ 1 (one_mem _), Units.val_mul, ← (nslMul k f).1 _ _ (toR δ).det_ne_zero hd, hv, (nslSl k f).1, hx, nsl_aff,
    ← mul_assoc, ← Complex.ofReal_mul, ← Real.rpow_add z.im_pos]
  simp

end UpperTheory.V.Br

open UpperTheory.V.Br in
theorem UpperTheory.V.Br.deadel :
    UpperTheory.V.Br.Deadel := by
  intro k N hN χ ω hω φ hc hlow hK hz
  haveI : NeZero N := ⟨by omega⟩
  have hlift := downLift k N hN φ hc.1.left hlow hK
  have hχ := downChar k N hN χ ω hω _ _ hlift hz
  refine ⟨⟨⟨down k φ.1, ?_⟩, downHol k φ hlow, ?_⟩, hχ, hlift⟩
  · rintro _ ⟨γ, hγ, rfl⟩
    have h1 := (Gamma1_mem N γ).1 hγ
    have h2 := hχ γ (Gamma0_mem.2 h1.2.2)
    rw [h1.2.1, map_one, one_smul] at h2
    exact h2
  · intro c hcu
    rw [Subgroup.IsArithmetic.isCusp_iff_isCusp_SL2Z] at hcu
    rw [OnePoint.isZeroAt_iff_forall_SL2Z hcu]
    intro γ _
    have := downZero k _ (cusp_fin hc (toF (Matrix.SpecialLinearGroup.mapGL ℚ γ))⁻¹) (isLow_fin hlow _)
    rw [down_fin hc.1.left hlift] at this
    exact this
end
end

