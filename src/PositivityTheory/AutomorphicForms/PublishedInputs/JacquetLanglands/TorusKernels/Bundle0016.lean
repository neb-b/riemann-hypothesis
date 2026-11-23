module

public import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf

@[expose] public section

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.HyperbolicOrbitIntegralProof
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Af UpperTheory.V.Sd UpperTheory.V.Sd.Wc Matrix

namespace UpperTheory.Esk.HyperbolicSetupLemmas

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

omit [IsTotallyReal F] in
theorem pow_char {ω : HChar F} (h : IsOfFinOrder ω) : ∃ n, 0 < n ∧ ∀ x, ω.1 x ^ n = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e2 : ω.1 ^ n = 1 := congrArg Subtype.val e
  exact ⟨n, hn, fun x => by rw [← MonoidHom.pow_apply, e2, MonoidHom.one_apply]⟩

theorem exp_triv {ω : HChar F} (h : IsOfFinOrder ω) (z : TR.Rinf F) : ω.1 (TR.infId F (TR.expU z)) = 1 := by
  obtain ⟨n, hn, e⟩ := isOfFinOrder_iff_pow_eq_one.1 h
  have e1 : TR.expU z = TR.expU ((n : ℝ)⁻¹ • z) ^ n := by
    refine Units.ext (funext fun i => ?_)
    have : (n : ℝ) ≠ 0 := by positivity
    simp only [Units.val_pow_eq_pow_val, Pi.pow_apply, TR.expU_val, ← Real.exp_nat_mul, Pi.smul_apply, smul_eq_mul]
    congr 1
    field_simp
  rw [e1, map_pow, map_pow]
  have e2 : ω.1 ^ n = 1 := congrArg Subtype.val e
  exact DFunLike.congr_fun e2 _

def pU : (TR.Rinf F)ˣ ≃* (InfinitePlace F → ℝˣ) := MulEquiv.piUnits

omit [NumberField F] [IsTotallyReal F] in
theorem pU_symm_val (f : InfinitePlace F → ℝˣ) (w : InfinitePlace F) :
    (((pU.symm f : (TR.Rinf F)ˣ) : TR.Rinf F) w) = (f w : ℝ) := rfl

omit [NumberField F] [IsTotallyReal F] in
theorem pU_val (s : (TR.Rinf F)ˣ) (w : InfinitePlace F) : ((pU s w : ℝˣ) : ℝ) = (s : TR.Rinf F) w := rfl


open Classical in
def atV (v : InfinitePlace F) (x : ℝˣ) : (TR.Rinf F)ˣ := pU.symm (Pi.mulSingle v x : InfinitePlace F → ℝˣ)

open Classical in
omit [NumberField F] [IsTotallyReal F] in
theorem atV_val (v w : InfinitePlace F) (x : ℝˣ) :
    ((atV v x : (TR.Rinf F)ˣ) : TR.Rinf F) w = (((Pi.mulSingle v x : InfinitePlace F → ℝˣ) w : ℝˣ) : ℝ) := pU_symm_val _ w

theorem atV_neg (v : InfinitePlace F) :
    TR.infId F (atV v (-1)) = ReciprocityTheory.Neutral.Bridge.HCFR.infIdele F v (-1) := by
  classical
  refine Units.ext (Prod.ext (funext fun w => ?_) ?_)
  · change (1 - TR.infEq F 1 + TR.infEq F ((atV v (-1) : (TR.Rinf F)ˣ) : TR.Rinf F)) w =
      Pi.mulSingle (M := fun w : InfinitePlace F => w.Completion) v (-1) w
    rw [map_one, sub_self, zero_add]
    change (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm
      (((atV v (-1) : (TR.Rinf F)ˣ) : TR.Rinf F) w) = _
    by_cases h : w = v
    · subst h
      have : ((atV w (-1) : (TR.Rinf F)ˣ) : TR.Rinf F) w = -1 := by rw [atV_val]; simp
      rw [this]
      simp
    · have : ((atV v (-1) : (TR.Rinf F)ˣ) : TR.Rinf F) w = 1 := by rw [atV_val, Pi.mulSingle_eq_of_ne h]; simp
      rw [this]
      simp [h]
  · change (1 : Af F) - 0 + 0 = 1
    simp

open Classical in
omit [IsTotallyReal F] in
theorem prod_atV (s : (TR.Rinf F)ˣ) : s = ∏ v, atV v (pU s v) := by
  simp only [atV]
  rw [← map_prod, Finset.univ_prod_mulSingle, MulEquiv.symm_apply_apply]

theorem inf_sign {k : InfinitePlace F → ℕ} {ω : HChar F} (hω : IsOfFinOrder ω) (hs : Sgn k ω) (u : (TR.Rinf F)ˣ) :
    ((ω.1 (TR.infId F u) : ℂˣ) : ℂ) = ∏ v, ((SignType.sign (u.val v) : ℝ) : ℂ) ^ k v := by
  obtain ⟨s, hss, e⟩ := TR.exists_sign_mul_expU u
  have hsv : ∀ v, (s : TR.Rinf F) v = 1 ∨ (s : TR.Rinf F) v = -1 := fun v => by
    have := congrArg (fun x : (TR.Rinf F)ˣ => (x : TR.Rinf F) v) hss
    simp only [Units.val_mul, Pi.mul_apply, Units.val_one, Pi.one_apply] at this
    exact mul_self_eq_one_iff.1 this
  have hsign : ∀ v, ((SignType.sign (u.val v) : ℝ)) = (s : TR.Rinf F) v := fun v => by
    have hu : u.val v = (s : TR.Rinf F) v * Real.exp (Real.log |u.val v|) := by
      conv_lhs => rw [e]
      simp [TR.expU_val]
    rw [hu, sign_mul, sign_pos (Real.exp_pos _), mul_one]
    rcases hsv v with h | h <;> rw [h] <;> simp
  have hL : ((ω.1 (TR.infId F u) : ℂˣ) : ℂ) = ∏ v, ((ω.1 (TR.infId F (atV v (pU s v))) : ℂˣ) : ℂ) := by
    have h1 : ω.1 (TR.infId F u) = ω.1 (TR.infId F s) := by
      rw [e, map_mul, map_mul, exp_triv hω, mul_one]
    rw [h1]
    conv_lhs => rw [prod_atV s]
    rw [map_prod, map_prod, Units.coe_prod]
  rw [hL]
  refine Finset.prod_congr rfl fun v _ => ?_
  rw [hsign v]
  have hpv : ((pU s v : ℝˣ) : ℝ) = (s : TR.Rinf F) v := pU_val s v
  rcases hsv v with h | h
  · have : pU s v = 1 := Units.ext (hpv.trans h)
    rw [this, h]
    simp [atV]
  · have : pU s v = -1 := Units.ext (by rw [hpv, h]; simp)
    rw [this, h, atV_neg]
    have := hs v
    rw [HChar.locInf] at this
    simpa using this

theorem pInf_alg (x : F) (v : InfinitePlace F) :
    TR.pInf F (algebraMap F (Ad F) x) v = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  change InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal v) (algebraMap F (InfiniteAdeleRing F) x v) = _
  simp

theorem fin_rat {k : InfinitePlace F → ℕ} {ω : HChar F} (hω : IsOfFinOrder ω) (hs : Sgn k ω) (a : Fˣ) :
    ((ω.1 (finId F (ratU F a)) : ℂˣ) : ℂ) =
      ∏ v, ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) ^ k v := by
  let φ : F →+* TR.Rinf F := (TR.pInf F).comp (algebraMap F (AdeleRing (𝓞 F) F))
  have e : TR.infId F (Units.map φ.toMonoidHom a) * finId F (ratU F a) =
      Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a := by
    refine Units.ext (TR.ad_ext ?_ ?_)
    · rw [Units.val_mul, map_mul]
      change TR.pInf F (1 - TR.sInf F 1 + TR.sInf F (φ a)) *
        TR.pInf F (1 - GlobalTheory.CuspRep.sFin F 1 + GlobalTheory.CuspRep.sFin F _) = φ a
      have h1 : ∀ x, TR.pInf F (TR.sInf F x) = x := fun x => (TR.infEq F).symm_apply_apply x
      have h2 : ∀ x, TR.pInf F (GlobalTheory.CuspRep.sFin F x) = 0 := fun x => map_zero (TR.infEq F).symm
      simp only [map_add (f := _), map_sub, map_one, h1, h2, sub_self, zero_add, sub_zero, add_zero, mul_one]
    · rw [Units.val_mul, map_mul]
      change ((1 : Af F) - 0 + 0) * ((1 : Af F) - 1 + algebraMap F (Af F) a) = algebraMap F (Af F) a
      simp only [sub_self, zero_add, sub_zero, add_zero, one_mul]
  have h1 : ω.1 (Units.map (algebraMap F (AdeleRing (𝓞 F) F)).toMonoidHom a) = 1 := ω.2.2 a
  rw [← e, map_mul] at h1
  have h2 := congrArg Units.val h1
  rw [Units.val_mul, Units.val_one, inf_sign hω hs] at h2
  have h3 : ∀ v, ((Units.map φ.toMonoidHom a : (TR.Rinf F)ˣ) : TR.Rinf F) v =
      InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F) := fun v => pInf_alg (a : F) v
  simp only [h3] at h2
  have hP : (∏ v, ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) ^ k v) *
      ∏ v, ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) ^ k v = 1 := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun v _ => ?_
    rw [← mul_pow]
    have : ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) *
        ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) = 1 := by
      have ha : InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F) ≠ 0 :=
        (map_ne_zero _).2 a.ne_zero
      rcases lt_or_gt_of_ne ha with h | h
      · rw [sign_neg h]; simp
      · rw [sign_pos h]; simp
    rw [this, one_pow]
  calc _ = (∏ v, ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) ^ k v) *
        ((∏ v, ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (a : F)) : ℝ) : ℂ) ^ k v) *
          ((ω.1 (finId F (ratU F a)) : ℂˣ) : ℂ)) := by rw [← mul_assoc, hP, one_mul]
    _ = _ := by rw [h2, mul_one]

end UpperTheory.Esk.HyperbolicSetupLemmas

open UpperTheory.Esk.HyperbolicSetupLemmas in
theorem UpperTheory.Esk.hyperbolic_orbit_integral_proof : UpperTheory.Esk.H0b := by
  intro F _ _ _ k c ω χ hω hχ
  refine ⟨?_, fun hs => ⟨?_, inf_sign hω hs⟩⟩
  · obtain ⟨n, hn, hp⟩ := pow_char hω
    refine ⟨n, hn, fun h => ?_⟩
    obtain ⟨⟨k', hk', z, hz⟩, h2⟩ := hχ h
    rw [h2 k' hk' z hz]
    exact hp _
  · intro γ h
    obtain ⟨h1, h2, h3⟩ := center_entries h
    have h0 : γ 0 0 ≠ 0 := fun e => γ.det_ne_zero (by rw [Matrix.det_fin_two, e, h1]; simp)
    set a : Fˣ := Units.mk0 _ h0 with ha
    have hz : jF F γ = zc F (ratU F a) := by
      refine Units.ext (Matrix.ext fun i j => ?_)
      change algebraMap F (Af F) (γ i j) = Matrix.scalar (Fin 2) (algebraMap F (Af F) (γ 0 0)) i j
      fin_cases i <;> fin_cases j <;> simp [h1, h2, ← h3]
    obtain ⟨-, hχ2⟩ := hχ ⟨jF F γ, (mkDat c χ).cenH γ h⟩
    have e := hχ2 1 (one_mem _) (ratU F a) (by rw [one_mul]; exact hz)
    change ((χ ⟨jF F γ, _⟩ : ℂˣ) : ℂ) = ∏ v, ((SignType.sign (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) (γ 0 0)) : ℝ) : ℂ) ^ k v
    rw [e, fin_rat hω hs a]
    rfl
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.HyperbolicRelationProof
section
noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk.IdeleSplittingLemmas

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

def zg (g : GL (Fin 2) (TR.Rinf F)) : InfinitePlace F → P := fun v => gv v g • iP

def Jg (k : InfinitePlace F → ℕ) (g : GL (Fin 2) (TR.Rinf F)) : ℂ := ∏ v, j1 (k v) (gv v g) iP

theorem Jg_ne (hB : B1b) (k : InfinitePlace F → ℕ) (g : GL (Fin 2) (TR.Rinf F)) : Jg k g ≠ 0 :=
  Finset.prod_ne_zero_iff.2 fun v _ => hB.2.1 _ _ _

theorem pInf_alg (x : F) (v : InfinitePlace F) :
    TR.pInf F (algebraMap F (Ad F) x) v = InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v) x := by
  have h : algebraMap F (InfiniteAdeleRing F) x = TR.infEq F (fun w => InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x) := by
    funext w
    apply (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).injective
    show _ = (InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w))
      ((InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal w)).symm
        (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w) x))
    rw [RingEquiv.apply_symm_apply]
    simp
  change (TR.infEq F).symm (algebraMap F (InfiniteAdeleRing F) x) v = _
  rw [h, RingEquiv.symm_apply_apply]

theorem gv_rat (γ : GL (Fin 2) F) (v : InfinitePlace F) :
    gv v (Matrix.GeneralLinearGroup.map (TR.pInf F) (ratGL F 2 γ)) =
      Matrix.GeneralLinearGroup.map (InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal v)) γ :=
  Units.ext (Matrix.ext fun i j => pInf_alg (γ i j) v)

omit [IsTotallyReal F] in
theorem pFin_rat (γ : GL (Fin 2) F) : Matrix.GeneralLinearGroup.map (pFin F) (ratGL F 2 γ) = jF F γ :=
  Units.ext (Matrix.ext fun _ _ => rfl)

theorem val_eq (hB : B1b) {k : InfinitePlace F → ℕ} {f : (InfinitePlace F → P) × GF F → ℂ} {φ : GA F 2 → ℂ}
    (hr : Rel k f φ) (h : GA F 2) :
    φ h = f (zg (Matrix.GeneralLinearGroup.map (TR.pInf F) h), Matrix.GeneralLinearGroup.map (pFin F) h) /
      Jg k (Matrix.GeneralLinearGroup.map (TR.pInf F) h) := by
  rw [eq_div_iff (Jg_ne hB k _)]
  have := hr (Matrix.GeneralLinearGroup.map (TR.pInf F) h) (Matrix.GeneralLinearGroup.map (pFin F) h)
  rwa [TR.infGL_mul_finGL] at this

theorem part1 (hB : B1b) {k : InfinitePlace F → ℕ} {c : Pl F → ℕ} {χ : Hc c →* ℂˣ} {f : (InfinitePlace F → P) × GF F → ℂ}
    {φ : GA F 2 → ℂ} (hf : (mkDat c χ).IsForm k f) (hr : Rel k f φ) (γ : GL (Fin 2) F) (g : GA F 2) :
    φ (ratGL F 2 γ * g) = φ g := by
  rw [val_eq hB hr, val_eq hB hr, map_mul, map_mul, pFin_rat]
  set a := Matrix.GeneralLinearGroup.map (TR.pInf F) g
  set x := Matrix.GeneralLinearGroup.map (pFin F) g
  have hz : zg (Matrix.GeneralLinearGroup.map (TR.pInf F) (ratGL F 2 γ) * a) = (mkDat c χ).act γ (zg a) := by
    funext v
    simp only [zg, map_mul, gv_rat, mul_smul]
    rfl
  have hJ : Jg k (Matrix.GeneralLinearGroup.map (TR.pInf F) (ratGL F 2 γ) * a) = (mkDat c χ).J k γ (zg a) * Jg k a := by
    simp only [Jg, Dat.J, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    rw [map_mul, hB.1, gv_rat]
    rfl
  have hne : (mkDat c χ).J k γ (zg a) ≠ 0 := Finset.prod_ne_zero_iff.2 fun v _ => hB.2.1 _ _ _
  rw [hz, hJ, show jF F γ * x = (mkDat c χ).j γ * x from rfl, hf.aut, mul_div_mul_left _ _ hne]

theorem part2 (hB : B1b) {k : InfinitePlace F → ℕ} {c : Pl F → ℕ} {ω : HChar F} {χ : Hc c →* ℂˣ}
    {f : (InfinitePlace F → P) × GF F → ℂ} {φ : GA F 2 → ℂ} (hχ : IsChi c ω χ) (hf : (mkDat c χ).IsForm k f)
    (hr : Rel k f φ) (u : GF F) (hu : u ∈ Kc c) (g : GA F 2) : φ (g * finGL F 2 u) = φ g := by
  rw [val_eq hB hr, val_eq hB hr, map_mul, map_mul, TR.pInf_finGL, mul_one, pFin_finGL]
  have hH : u ∈ Hc c := Subgroup.mem_sup_left hu
  have h1 := hf.lev (zg (Matrix.GeneralLinearGroup.map (TR.pInf F) g)) (Matrix.GeneralLinearGroup.map (pFin F) g)
    (⟨u, hH⟩ : (mkDat c χ).H)
  have h2 : χ ⟨u, hH⟩ = 1 := by
    rw [(hχ ⟨u, hH⟩).2 u hu 1 (by simp [zc]), map_one, map_one]
  change f (_, _ * u) = (χ ⟨u, hH⟩ : ℂ) * _ at h1
  rw [h1, h2, Units.val_one, one_mul]

theorem idele_split (z : Ideles F) :
    TR.infId F (Units.map (TR.pInf F).toMonoidHom z) * finId F (Units.map (pFin F).toMonoidHom z) = z := by
  have h : ∀ x, TR.pInf F (TR.sInf F x) = x := fun x => (TR.infEq F).symm_apply_apply x
  have h2 : ∀ x, TR.pInf F (sFin F x) = 0 := fun x => map_zero (TR.infEq F).symm
  have h3 : ∀ x, pFin F (TR.sInf F x) = 0 := fun x => rfl
  have h4 : ∀ x, pFin F (sFin F x) = x := fun x => rfl
  refine Units.ext (TR.ad_ext ?_ ?_)
  · change TR.pInf F ((1 - TR.sInf F 1 + TR.sInf F (TR.pInf F z.val)) * (1 - sFin F 1 + sFin F (pFin F z.val))) = _
    simp [h, h2]
  · change pFin F ((1 - TR.sInf F 1 + TR.sInf F (TR.pInf F z.val)) * (1 - sFin F 1 + sFin F (pFin F z.val))) = _
    simp [h3, h4]

theorem map_scalar {R S : Type} [CommRing R] [CommRing S] (p : R →+* S) (z : Rˣ) :
    Matrix.GeneralLinearGroup.map p (Matrix.GeneralLinearGroup.scalar (Fin 2) z) =
      Matrix.GeneralLinearGroup.scalar (Fin 2) (Units.map p.toMonoidHom z) := by
  refine Units.ext (Matrix.ext fun i j => ?_)
  fin_cases i <;> fin_cases j <;> simp [Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map]

theorem sign_pow (k : ℕ) {s : ℝ} (hs : s ≠ 0) :
    s ^ k * |s * s| ^ (-(k : ℝ) / 2) = (SignType.sign s : ℝ) ^ k := by
  have ha : 0 < |s| := abs_pos.2 hs
  have e1 : |s * s| ^ (-(k : ℝ) / 2) = (|s| ^ k)⁻¹ := by
    rw [abs_mul, ← sq, ← Real.rpow_natCast |s| 2, ← Real.rpow_mul ha.le, ← Real.rpow_natCast, ← Real.rpow_neg ha.le]
    congr 1
    push_cast
    ring
  rw [e1]
  calc s ^ k * (|s| ^ k)⁻¹ = ((SignType.sign s : ℝ) * |s|) ^ k * (|s| ^ k)⁻¹ := by rw [sign_mul_abs]
    _ = _ := by rw [mul_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ha.ne'), mul_one]

theorem automorphy_factor_scalar_matrix (k : ℕ) (g : GL (Fin 2) ℝ) (s : ℝ) (hs : s ≠ 0) (h10 : g 1 0 = 0) (h01 : g 0 1 = 0) (h00 : g 0 0 = s)
    (h11 : g 1 1 = s) (w : P) : j1 k g w = ((SignType.sign s : ℝ) : ℂ) ^ k := by
  rw [j1, den, det_eq, h10, h01, h00, h11, ← Complex.ofReal_pow, ← sign_pow k hs]
  simp [Complex.ofReal_mul]

theorem gv_scalar (t : (TR.Rinf F)ˣ) (v : InfinitePlace F) :
    (gv v (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) 1 0 = 0 ∧ (gv v (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) 0 1 = 0 ∧
      (gv v (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) 0 0 = t.val v ∧
      (gv v (Matrix.GeneralLinearGroup.scalar (Fin 2) t)) 1 1 = t.val v := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [gv, Matrix.GeneralLinearGroup.scalar, Matrix.GeneralLinearGroup.map]

theorem part3 (hB : B1b) (h0 : H0b) {k : InfinitePlace F → ℕ} {c : Pl F → ℕ} {ω : HChar F} {χ : Hc c →* ℂˣ}
    {f : (InfinitePlace F → P) × GF F → ℂ} {φ : GA F 2 → ℂ} (hω : IsOfFinOrder ω) (hχ : IsChi c ω χ) (hs : Sgn k ω)
    (hf : (mkDat c χ).IsForm k f) (hr : Rel k f φ) (z : Ideles F) (g : GA F 2) :
    φ (Matrix.GeneralLinearGroup.scalar (Fin 2) z * g) = ((ω.1 z : ℂˣ) : ℂ) * φ g := by
  set zi := Units.map (TR.pInf F).toMonoidHom z
  set zf := Units.map (pFin F).toMonoidHom z
  have hω' : ((ω.1 z : ℂˣ) : ℂ) = ((ω.1 (TR.infId F zi) : ℂˣ) : ℂ) * ((ω.1 (finId F zf) : ℂˣ) : ℂ) := by
    rw [← Units.val_mul, ← map_mul, idele_split]
  have hS := ((h0 F k c ω χ hω hχ).2 hs).2 zi
  rw [val_eq hB hr, val_eq hB hr g, map_mul, map_mul, map_scalar, map_scalar]
  set a := Matrix.GeneralLinearGroup.map (TR.pInf F) g
  set x := Matrix.GeneralLinearGroup.map (pFin F) g
  set S : ℂ := ∏ v, ((SignType.sign (zi.val v) : ℝ) : ℂ) ^ k v
  have hz : zg (Matrix.GeneralLinearGroup.scalar (Fin 2) zi * a) = zg a := by
    funext v
    obtain ⟨e1, e2, e3, e4⟩ := gv_scalar zi v
    simp only [zg, map_mul, mul_smul]
    exact center_smul _ e2 e1 (e3.trans e4.symm) _
  have hJ : Jg k (Matrix.GeneralLinearGroup.scalar (Fin 2) zi * a) = S * Jg k a := by
    simp only [Jg, S, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun v _ => ?_
    obtain ⟨e1, e2, e3, e4⟩ := gv_scalar zi v
    rw [map_mul, hB.1, automorphy_factor_scalar_matrix _ _ (zi.val v) (TR.unit_ne_zero zi v) e1 e2 e3 e4]
  have hH : zc F zf ∈ Hc c := Subgroup.mem_sup_right ⟨zf, rfl⟩
  have hc : χ ⟨zc F zf, hH⟩ = ω.1 (finId F zf) := (hχ ⟨zc F zf, hH⟩).2 1 (one_mem _) zf (one_mul _).symm
  have hl := hf.lev (zg a) x (⟨zc F zf, hH⟩ : (mkDat c χ).H)
  change f (_, x * zc F zf) = (χ ⟨zc F zf, hH⟩ : ℂ) * _ at hl
  have hcomm : Matrix.GeneralLinearGroup.scalar (Fin 2) zf * x = x * zc F zf :=
    (Subgroup.mem_center_iff.1 (zc_center zf) x).symm
  have hSS : S * S = 1 := by
    simp only [S, ← Finset.prod_mul_distrib, ← mul_pow]
    refine Finset.prod_eq_one fun v _ => ?_
    rcases lt_or_gt_of_ne (TR.unit_ne_zero zi v) with h | h
    · simp [h]
    · simp [h]
  have hSne : S ≠ 0 := left_ne_zero_of_mul_eq_one hSS
  rw [hz, hJ, hcomm, hl, hc, hω', hS, div_eq_iff (mul_ne_zero hSne (Jg_ne hB k a))]
  rw [show S * ((ω.1 (finId F zf) : ℂˣ) : ℂ) * (f (zg a, x) / Jg k a) * (S * Jg k a) =
    (S * S) * ((ω.1 (finId F zf) : ℂˣ) : ℂ) * f (zg a, x) * ((Jg k a)⁻¹ * Jg k a) by ring, hSS,
    inv_mul_cancel₀ (Jg_ne hB k a)]
  ring

theorem part4 (hB : B1b) {k : InfinitePlace F → ℕ} {c : Pl F → ℕ} {χ : Hc c →* ℂˣ}
    {f : (InfinitePlace F → P) × GF F → ℂ} {φ : GA F 2 → ℂ} (hf : (mkDat c χ).IsForm k f) (hr : Rel k f φ) :
    ∃ C, ∀ g, ‖φ g‖ ≤ C := by
  obtain ⟨C, hC⟩ := hf.bdd
  refine ⟨C, fun h => ?_⟩
  rw [val_eq hB hr h, norm_div]
  set a := Matrix.GeneralLinearGroup.map (TR.pInf F) h
  have hn : ‖Jg k a‖ * nrm k (zg a) = 1 := by
    rw [Jg, nrm, norm_prod, ← Finset.prod_mul_distrib]
    refine Finset.prod_eq_one fun v _ => ?_
    rw [zg, hB.2.2.2.2.1]
    simp [iP]
  have hpos : 0 < ‖Jg k a‖ := norm_pos_iff.2 (Jg_ne hB k a)
  rw [div_le_iff₀ hpos]
  have := hC (zg a) (Matrix.GeneralLinearGroup.map (pFin F) h)
  calc _ = ‖f (zg a, Matrix.GeneralLinearGroup.map (pFin F) h)‖ * nrm k (zg a) * ‖Jg k a‖ := by
        rw [mul_assoc, mul_comm (nrm k _), hn, mul_one]
    _ ≤ C * ‖Jg k a‖ := mul_le_mul_of_nonneg_right this hpos.le

end UpperTheory.Esk.IdeleSplittingLemmas

theorem UpperTheory.Esk.hyperbolic_relation_proof : UpperTheory.Esk.B1b → UpperTheory.Esk.H0b → UpperTheory.Esk.H2a := by
  intro hB h0 F _ _ _ k c _ ω χ hω hχ hs _ f φ hf hr
  exact ⟨UpperTheory.Esk.IdeleSplittingLemmas.part1 hB hf hr, UpperTheory.Esk.IdeleSplittingLemmas.part2 hB hχ hf hr,
    UpperTheory.Esk.IdeleSplittingLemmas.part3 hB h0 hω hχ hs hf hr, UpperTheory.Esk.IdeleSplittingLemmas.part4 hB hf hr⟩
end
end

-- bundled from PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.PfGUnit
section
noncomputable section

open NumberField IsDedekindDomain UpperTheory.V.Sd.Wc
open scoped NNReal

namespace UpperTheory.Esk.NormOneUnitsLemmas

theorem pow_sub (ν : Valuation ℂ ℝ≥0) {b : ℂ} (hb : ν b ≤ 1) (m : ℕ) : ν (b ^ m - 1) ≤ ν (b - 1) := by
  rw [← geom_sum_mul, Valuation.map_mul]
  refine mul_le_of_le_one_left zero_le ?_
  refine Valuation.map_sum_le _ fun i _ => ?_
  rw [Valuation.map_pow]
  exact pow_le_one₀ zero_le hb

theorem pow_l (ν : Valuation ℂ ℝ≥0) (l : ℕ) {b : ℂ} (hb : ν b ≤ 1) (hbp : ν (b - 1) ≤ ν (l : ℂ)) :
    ν (b ^ l - 1) ≤ ν (l : ℂ) * ν (b - 1) := by
  rw [← geom_sum_mul, Valuation.map_mul]
  refine mul_le_mul_of_nonneg_right ?_ zero_le
  have e : ∑ i ∈ Finset.range l, b ^ i = ∑ i ∈ Finset.range l, (b ^ i - 1) + (l : ℂ) := by
    rw [Finset.sum_sub_distrib]; simp
  rw [e]
  refine (Valuation.map_add _ _ _).trans (max_le ?_ le_rfl)
  exact Valuation.map_sum_le _ fun i _ => (pow_sub ν hb i).trans hbp

theorem pow_lN (ν : Valuation ℂ ℝ≥0) (l : ℕ) {b : ℂ} (hb : ν b ≤ 1) (hbp : ν (b - 1) ≤ ν (l : ℂ)) :
    ∀ N : ℕ, ν (b ^ (l ^ N) - 1) ≤ ν (l : ℂ) ^ N * ν (b - 1)
  | 0 => by simp
  | N + 1 => by
    have hb' : ν (b ^ (l ^ N)) ≤ 1 := by rw [Valuation.map_pow]; exact pow_le_one₀ zero_le hb
    have e : b ^ (l ^ (N + 1)) = (b ^ (l ^ N)) ^ l := by rw [pow_succ, pow_mul]
    rw [e]
    refine (pow_l ν l hb' ((pow_sub ν hb _).trans hbp)).trans ?_
    rw [pow_succ', mul_assoc]
    exact mul_le_mul_of_nonneg_left (pow_lN ν l hb hbp N) zero_le

theorem lt_one_le (a : WithZero (Multiplicative ℤ)) (h : a < 1) : a ≤ WithZero.exp (-1 : ℤ) := by
  by_cases h0 : a = 0
  · rw [h0]; exact zero_le
  · rw [← WithZero.exp_log h0] at h ⊢
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [WithZero.exp_le_exp]
    omega

end UpperTheory.Esk.NormOneUnitsLemmas

open UpperTheory.Esk.NormOneUnitsLemmas in
theorem UpperTheory.Esk.pf_GUnit : UpperTheory.Esk.GUnit := by
  intro F _ _ l _ ι D v x hx N t ht
  obtain ⟨m, rfl⟩ := ht
  set L : (D.pl v).adicCompletion F := ((l : ℕ) : (D.pl v).adicCompletion F) with hL
  have hLv : Valued.v L = WithZero.exp (-1 : ℤ) := D.unif v
  have hL0 : L ≠ 0 := fun h => by rw [h, map_zero] at hLv; exact WithZero.exp_ne_zero hLv.symm
  have hemL : D.em v L = (l : ℂ) := map_natCast _ l
  have hxle : nu ι (D.em v x) ≤ 1 := (D.le v x).2 hx.le
  set y := x ^ (l - 1) - 1 with hy
  have hemy : D.em v y = D.em v x ^ (l - 1) - 1 := by rw [hy, map_sub, map_pow, map_one]
  have hylt : Valued.v y < 1 := (D.lt v y).1 (by rw [hemy]; exact D.res v x hx)
  have hyL : Valued.v (y / L) ≤ 1 := by
    rw [map_div₀, hLv, div_le_one₀ (by simp)]
    exact lt_one_le _ hylt
  have hnuy : nu ι (D.em v y) ≤ nu ι (l : ℂ) := by
    have e : y = L * (y / L) := by field_simp
    rw [e, map_mul, map_mul, hemL]
    exact mul_le_of_le_one_right zero_le ((D.le v _).2 hyL)
  rw [hemy] at hnuy
  set a := D.em v x ^ (l - 1) with ha
  have hale : nu ι a ≤ 1 := by rw [ha, Valuation.map_pow]; exact pow_le_one₀ zero_le hxle
  have ha1 : nu ι (a - 1) ≤ 1 := by rw [← hemy]; exact ((D.lt v y).2 hylt).le
  have e : D.em v x ^ ((l - 1) * l ^ N * m) = (a ^ (l ^ N)) ^ m := by rw [ha, ← pow_mul, ← pow_mul, mul_assoc]
  rw [e]
  have hb : nu ι (a ^ (l ^ N)) ≤ 1 := by rw [Valuation.map_pow]; exact pow_le_one₀ zero_le hale
  refine (pow_sub _ hb m).trans ((pow_lN _ l hale hnuy N).trans ?_)
  exact mul_le_of_le_one_right zero_le ha1
end
end

