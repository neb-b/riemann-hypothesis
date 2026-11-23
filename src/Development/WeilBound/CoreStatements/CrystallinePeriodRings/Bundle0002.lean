module

public import Mathlib
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.ExistsMapEqOfPowMul
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.Bundle0001
public import GroundTheory.PAdicHodge.Bundle0007
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.LocTied6
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.AinfMapSurjective
public import Development.WeilBound.CoreStatements.CrystallinePeriodRings.InstCommRingBcris

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.CrystallinePeriodRings.InvRestrictScalarsMem
section
noncomputable section

namespace PositivityTheory.LocInh

open GroundTheory.PAdicHodge Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

section Abstract

theorem inv_away_range {A E : Type} [CommRing A] [Field E] {a : A}
    (F : Localization.Away a →+* E) (f : A → E)
    (h : ∀ x, F (algebraMap A (Localization.Away a) x) = f x) {k : ℕ} {y : A} {z : E}
    (e : f y = f a ^ k * z) : ∃ x, F x = z := by
  rw [← h, ← h] at e
  exact exists_map_eq_of_pow_mul F (IsLocalization.Away.algebraMap_isUnit a) e

theorem inv_map_frac {A B E : Type} [CommRing A] [CommRing B] [Field E] {F : B →+* E} {f : A →+* B}
    {g : A →+* E} (h : Fac F f g) {a t y : A} {m n : ℕ} {x : B} (e : f a ^ m * f t ^ n * x = f y) :
    g y = g a ^ m * (g t ^ n * F x) := by
  have h1 := congrArg F e
  rw [map_mul, map_mul, map_pow, map_pow, h, h, h] at h1
  rw [← h1, mul_assoc]

theorem inv_equivariant {A B E : Type} [CommRing A] [CommRing B] [Field E] {F : B →+* E}
    {f : A →+* B} {g : A →+* E} (h : Fac F f g) {a t : A} (hf : IsFrac f a t) {s : B →+* B}
    {s₀ : A →+* A} (hs : s.comp f = f.comp s₀) (τ : E ≃+* E) (hτ : ∀ x, g (s₀ x) = τ (g x))
    (b : B) : F (s b) = τ (F b) := by
  have e : F.comp s = (τ : E →+* E).comp F := by
    refine hf.hom_ext fun x => ?_
    have h1 : s (f x) = f (s₀ x) := RingHom.congr_fun hs x
    rw [RingHom.comp_apply, RingHom.comp_apply, h1, h, h, hτ, RingHom.coe_coe]
  exact RingHom.congr_fun e b

end Abstract

section Restrict

variable {p : ℕ} [Fact p.Prime] {K L : IntermediateField ℚ_[p] (PadicAlgCl p)}

theorem inv_galCp_congr (σ : Gal(PadicAlgCl p/K)) (τ : Gal(PadicAlgCl p/L)) (h : ∀ x, σ x = τ x) :
    (galCp σ : ℂ_[p] →+* ℂ_[p]) = (galCp τ : ℂ_[p] →+* ℂ_[p]) :=
  RingHom.ext (congrFun (eq_galCp_of_continuous τ (galCp σ) (continuous_galCp σ)
    fun y => by rw [galCp_coe, h]))

theorem inv_galMap_congr (σ : Gal(PadicAlgCl p/K)) (τ : Gal(PadicAlgCl p/L)) (h : ∀ x, σ x = τ x) :
    AInf.galMap σ = AInf.galMap τ :=
  AInf.map_congr (inv_galCp_congr σ τ h) _ _

theorem inv_galAway_congr (σ : Gal(PadicAlgCl p/K)) (τ : Gal(PadicAlgCl p/L)) (h : ∀ x, σ x = τ x) :
    galAway σ = galAway τ :=
  IsLocalization.ringHom_ext (Submonoid.powers (p : AInf ℂ_[p] p)) (RingHom.ext fun w => by
    rw [RingHom.comp_apply, RingHom.comp_apply, galAway_algebraMap, galAway_algebraMap,
      AInf.gal_smul_def, AInf.gal_smul_def, inv_galMap_congr σ τ h])

theorem inv_galQuot_congr (σ : Gal(PadicAlgCl p/K)) (τ : Gal(PadicAlgCl p/L)) (h : ∀ x, σ x = τ x)
    (n : ℕ) : galQuot σ n = galQuot τ n :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun a => by
    simp only [RingHom.comp_apply, galQuot_mk, inv_galAway_congr σ τ h])

theorem inv_galBdRHom_congr (σ : Gal(PadicAlgCl p/K)) (τ : Gal(PadicAlgCl p/L))
    (h : ∀ x, σ x = τ x) (x : BDeRhamPlus (normInteger ℂ_[p]) p) :
    galBdRHom σ x = galBdRHom τ x :=
  IsPerfectoidField.evalB_ext fun n => by
    rw [evalB_galBdRHom, evalB_galBdRHom, inv_galQuot_congr σ τ h]

theorem inv_galBdRField_congr (σ : Gal(PadicAlgCl p/K)) (τ : Gal(PadicAlgCl p/L))
    (h : ∀ x, σ x = τ x) : galBdRField σ = galBdRField τ := by
  have e : galBdR σ = galBdR τ := RingEquiv.ext fun x => by
    rw [galBdR_apply, galBdR_apply, gal_smul_bdR_def, gal_smul_bdR_def, inv_galBdRHom_congr σ τ h]
  unfold galBdRField
  rw [e]

end Restrict

variable {l : ℕ} [Fact l.Prime]

theorem inv_galBdRField_eq {K : IntermediateField ℚ_[l] (Om l)} (σ : Gal(PadicAlgCl l/K)) :
    galBdRField σ = Per6.σD (σ.restrictScalars ℚ_[l]) :=
  inv_galBdRField_congr σ (Per6.toBot (σ.restrictScalars ℚ_[l])) fun _ => rfl

theorem inv_restrictScalars_mem (K : FinExt l) (σ : Gal(PadicAlgCl l/K.1)) :
    σ.restrictScalars ℚ_[l] ∈ GK K :=
  (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx => σ.commutes ⟨x, hx⟩

theorem invD (K : FinExt l) (b : Per6.BdR l) (hb : ∀ g ∈ GK K, Per6.σD g b = b) :
    ∃ c ∈ K.1, oD l c = b := by
  have := K.2
  obtain ⟨k, hk⟩ := bDeRham_fixed K.1 b fun σ => by
    rw [gal_smul_bDeRham_def, inv_galBdRField_eq]
    exact hb _ (inv_restrictScalars_mem K σ)
  exact ⟨k.1, k.2, hk⟩

theorem inv_cD_galCris (g : GQ l) (x : ACris.ACris ℂ_[l] l) :
    cD l (ACris.galCris (Per6.toBot g) x) = Per6.σD g (cD l x) := by
  rw [cD_apply, cD_apply, ← ACris.gal_smul_def, ACris.iota_gal_smul]
  exact (galBdRField_algebraMap _ _).symm

theorem inv_ιCD_σB (g : GQ l) (b : Per6.Bcris l) : ιCD l (Per6.σB g b) = Per6.σD g (ιCD l b) :=
  inv_equivariant (ιCD_fac l) (cB_isFrac l) (σB_comp g) (Per6.σD g) (inv_cD_galCris g) b


variable (l) in
def invPlusD : ACris.BCrisPlus ℂ_[l] l →+* Per6.BdR l :=
  (algebraMap (Per6.BdRp l) (Per6.BdR l)).comp (ACris.iotaPlus ℂ_[l] l)

theorem invPlusD_algebraMap (x : ACris.ACris ℂ_[l] l) :
    invPlusD l (algebraMap (ACris.ACris ℂ_[l] l) (ACris.BCrisPlus ℂ_[l] l) x) = cD l x :=
  congrArg (algebraMap (Per6.BdRp l) (Per6.BdR l)) (ACris.iotaPlus_algebraMap x)

theorem inv_exists_plus (b : Per6.Bcris l) : ∃ (n : ℕ) (y : ACris.BCrisPlus ℂ_[l] l),
    invPlusD l y = cD l (Per6.tA l) ^ n * ιCD l b := by
  obtain ⟨m, n, y, h⟩ := bcris_surj b
  exact ⟨n, inv_away_range (invPlusD l) (cD l) invPlusD_algebraMap (inv_map_frac (ιCD_fac l) h)⟩

set_option maxHeartbeats 1600000 in
theorem inv_exists_iotaB {ε : PreTilt (normInteger ℂ_[l]) l} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv (PreTilt (normInteger ℂ_[l]) l) l).symm ε) ≠ 1)
    {n : ℕ} {y : ACris.BCrisPlus ℂ_[l] l} {z : Per6.BdR l}
    (h : invPlusD l y = cD l (ACris.periodT hε) ^ n * z) :
    ∃ x : ACris.BCris hε, ACris.iotaB hε hζ x = z :=
  inv_away_range (ACris.iotaB hε hζ) (invPlusD l) (ACris.iotaB_algebraMap hε hζ)
    (h.trans (congrArg (· ^ n * z) (invPlusD_algebraMap (ACris.periodT hε)).symm))

set_option maxHeartbeats 1600000 in
theorem inv_mem_Kur {b : Per6.Bcris l} {c : Om l} (h : oD l c = ιCD l b) : c ∈ MaximalUnramifiedExtension l := by
  obtain ⟨n, y, hy⟩ := inv_exists_plus b
  rw [← h] at hy
  rw [kur_eq]
  exact (ACris.exists_iotaB_eq_iff untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one).1
    (inv_exists_iotaB untilt_epsilon untilt_frobeniusEquiv_symm_epsilon_ne_one hy)

theorem invB (K : FinExt l) (b : Per6.Bcris l) (hb : ∀ g ∈ GK K, Per6.σB g b = b) :
    ∃ c : ↥(MaximalUnramifiedExtension l), (c : Om l) ∈ K.1 ∧ uB l c = b := by
  obtain ⟨c, hc, h⟩ := invD K (ιCD l b) fun g hg =>
    (inv_ιCD_σB g b).symm.trans (congrArg (ιCD l) (hb g hg))
  exact ⟨⟨c, inv_mem_Kur h⟩, hc, ιCD_injective ((ιCD_uB _).trans h)⟩

end PositivityTheory.LocInh
end
end

-- bundled from Development.WeilBound.CoreStatements.CrystallinePeriodRings.MaximalIdealEqSpanT
section
noncomputable section

namespace PositivityTheory.LocInh

open GroundTheory.PAdicHodge Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

theorem actC_eq (AI : LocAinf l P) (g : GQ l) (y : ℂ_[l]) : AI.actC g y = actC l g y :=
  congrFun (eq_galCp_of_continuous (Per6.toBot g) (AI.actC g)
    (AddMonoidHomClass.isometry_of_norm (AI.actC g) (AI.actC_norm g)).continuous
    (AI.actC_ext g)) y

theorem tiltMap_ε (AI : LocAinf l P) : Per6.tiltMap l AI.ε =
    IsPerfectoidField.ofCompatible l (fun n => Per6.intEquiv l (AI.ζ n))
      (fun n => by rw [← map_pow, AI.ζ_succ]) :=
  Perfection.ext fun n => frob_coeff_tiltMap AI.ε n (AI.ζ n) (AI.ε_coeff n)

theorem untilt_ε (AI : LocAinf l P) : PreTilt.untilt (Per6.tiltMap l AI.ε) = 1 := by
  rw [tiltMap_ε, IsPerfectoidField.untilt_ofCompatible, AI.ζ_zero, map_one]

theorem untilt_ε_root (AI : LocAinf l P) :
    PreTilt.untilt ((frobeniusEquiv (PreTilt ↥(normInteger ℂ_[l]) l) l).symm
      (Per6.tiltMap l AI.ε)) = Per6.intEquiv l (AI.ζ 1) := by
  rw [tiltMap_ε, AInf.frobeniusEquiv_symm_ofCompatible, IsPerfectoidField.untilt_ofCompatible]

theorem untilt_ε_root_ne_one (AI : LocAinf l P) :
    PreTilt.untilt ((frobeniusEquiv (PreTilt ↥(normInteger ℂ_[l]) l) l).symm
      (Per6.tiltMap l AI.ε)) ≠ 1 := by
  rw [untilt_ε_root]
  exact fun h => AI.ζ_one ((Per6.intEquiv l).injective (h.trans (map_one _).symm))

theorem ιB_algebraMap_K0 (P : LocPrime l) (K : FinExt l) (c : ↥(K0 K)) :
    P.ιB (algebraMap ↥(K0 K) P.R.B c) = algebraMap (Om l) P.R.BdR (c : Om l) :=
  (P.PD_ι K _).symm.trans ((P.PD K).ι.commutes c)

theorem ιB_algebraMap (P : LocPrime l) (c : ↥(MaximalUnramifiedExtension l)) :
    P.ιB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = algebraMap (Om l) P.R.BdR (c : Om l) :=
  ιB_algebraMap_K0 P ⟨IntermediateField.adjoin ℚ_[l] {(c : Om l)},
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral _)⟩
    ⟨c, IntermediateField.subset_adjoin _ _ (Set.mem_singleton _), c.2⟩

variable (T : LocTied6 l P AI)

theorem tie_ι (b : P.R.B) : T.eD (P.ιB b) = ιCD l (T.eB b) := by
  have h := RingHom.congr_fun ((isCrisDR_iff _).1 T.incl) (T.eB b)
  rw [← h]
  simp

theorem tie_a (a : Ainf l) :
    T.eD (P.ιB (AI.ιA a)) = algebraMap (Per6.BdRp l) (Per6.BdR l) (Per6.aD l a) := by
  rw [tie_ι, T.ιA, ιCD_aB]

theorem tie_qD (q : ℚ_[l]) :
    T.eD (algebraMap ℚ_[l] P.R.BdR q) = oD l (algebraMap ℚ_[l] (Om l) q) :=
  RingHom.congr_fun (IsLocalization.ringHom_ext (nonZeroDivisors ℤ_[l]) (S := ℚ_[l])
    (j := T.eD.toRingHom.comp (algebraMap ℚ_[l] P.R.BdR))
    (k := (oD l).comp (algebraMap ℚ_[l] (Om l)))
    (RingHom.ext fun z => (T.zD z).trans (oD_coe z).symm)) q

theorem tie_o (x : Om l) : T.eD (algebraMap (Om l) P.R.BdR x) = oD l x := by
  choose y hy hθ using T.om
  have hj := IsPerfectoidField.algebraMap_bDeRham_injective (K := ℂ_[l]) (p := l)
  let f : Om l →ₐ[ℚ_[l]] Per6.BdRp l :=
    { toFun := y
      map_one' := hj (by rw [← hy, map_one, map_one, map_one])
      map_mul' := fun a b => hj (by rw [← hy, map_mul, map_mul, map_mul, hy, hy])
      map_zero' := hj (by rw [← hy, map_zero, map_zero, map_zero])
      map_add' := fun a b => hj (by rw [← hy, map_add (f := _), map_add (f := _), map_add (f := _), hy, hy])
      commutes' := fun q => hj (by
        rw [← hy, ← IsScalarTower.algebraMap_apply, tie_qD, frob_oD_apply, AlgHom.commutes]) }
  have hf : f = algClToBdR l := eq_algClToBdR l f hθ
  rw [hy, frob_oD_apply, ← hf]
  rfl

theorem tie_u (c : ↥(MaximalUnramifiedExtension l)) : T.eB (algebraMap ↥(MaximalUnramifiedExtension l) P.R.B c) = uB l c :=
  ιCD_injective (by rw [← tie_ι, ιB_algebraMap, tie_o, ιCD_uB])

theorem tie_q (q : ℚ_[l]) : T.eB (algebraMap ℚ_[l] P.R.B q) = qB l q := by
  rw [IsScalarTower.algebraMap_apply ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B, tie_u, uB_algebraMap]

theorem tie_t : T.eD (P.ιB P.tB) =
    algebraMap (Per6.BdRp l) (Per6.BdR l) (fontaineT (Per6.tiltMap l AI.ε) (untilt_ε AI)) := by
  obtain ⟨y, hy, h⟩ := T.t
  obtain ⟨_, rfl⟩ := (isLog_iff _ _).1 hy
  exact h

theorem maximalIdeal_eq_span_t (AI : LocAinf l P) : IsLocalRing.maximalIdeal (Per6.BdRp l) =
    Ideal.span {fontaineT (Per6.tiltMap l AI.ε) (untilt_ε AI)} :=
  maximalIdeal_eq_span_fontaineT (untilt_ε AI) (untilt_ε_root_ne_one AI)

theorem tie_fil_zero (K : FinExt l) (x : P.R.BdR) : x ∈ (P.PD K).Fil 0 ↔
    ∃ y : Per6.BdRp l, T.eD x = algebraMap (Per6.BdRp l) (Per6.BdR l) y :=
  (T.fil K 0 x).trans (IsPerfectoidField.mem_fil_zero_iff ℂ_[l] l)

end PositivityTheory.LocInh
end
end

