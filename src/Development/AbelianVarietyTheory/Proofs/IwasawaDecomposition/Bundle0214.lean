module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ContinuousMapPFin
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0207
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormDwLeSobNorm
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlace
public import Formalism.LocalToGlobal.BesselHermitianTheta.AllTied
public import Formalism.LocalToGlobal.IndefiniteReal.Bundle0016
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.AdelicDataRowMeasureScaleTrivialTuple

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryArchimedean
section
noncomputable section

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory.DefU

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

def evGL (w : InfinitePlace E) : GL (Fin n) (Cinf E) →* GL (Fin n) ℂ :=
  GeneralLinearGroup.map (Pi.evalRingHom (fun _ => ℂ) w)

theorem gl_ext_evGL {a b : GL (Fin n) (Cinf E)} (h : ∀ w, evGL w a = evGL w b) : a = b := by
  ext i j w
  exact congrArg (fun x : GL (Fin n) ℂ => x i j) (h w)


open Classical in
def atPlace (v : InfinitePlace E) : Cinf E →ₙ+* Cinf E where
  toFun x := Pi.single v (x v)
  map_mul' x y := Pi.single_mul (α := fun _ : InfinitePlace E => ℂ) v (x v) (y v)
  map_zero' := Pi.single_zero (M := fun _ : InfinitePlace E => ℂ) v
  map_add' x y := Pi.single_add (f := fun _ : InfinitePlace E => ℂ) v (x v) (y v)

theorem atPlace_self (v : InfinitePlace E) (x : Cinf E) : atPlace v x v = x v := by
  classical
  exact Pi.single_eq_same (M := fun _ : InfinitePlace E => ℂ) v (x v)

theorem atPlace_of_ne {v w : InfinitePlace E} (h : w ≠ v) (x : Cinf E) : atPlace v x w = 0 := by
  classical
  exact Pi.single_eq_of_ne (M := fun _ : InfinitePlace E => ℂ) h (x v)

def cutGL (v : InfinitePlace E) : GL (Fin n) (Cinf E) →* GL (Fin n) (Cinf E) := cornerGL n (atPlace v)

theorem evGL_cutGL_self (v : InfinitePlace E) (y : GL (Fin n) (Cinf E)) : evGL v (cutGL v y) = evGL v y :=
  map_cornerGL_of_hom _ _ _ (fun x => atPlace_self v x) y

theorem evGL_cutGL_of_ne {v w : InfinitePlace E} (h : w ≠ v) (y : GL (Fin n) (Cinf E)) :
    evGL w (cutGL v y) = 1 :=
  map_cornerGL_of_zero _ _ (fun x => atPlace_of_ne h x) y

theorem unitary_iff_evGL (y : GL (Fin n) (Cinf E)) :
    y.valᴴ * y.val = 1 ↔ ∀ w, (evGL w y).valᴴ * (evGL w y).val = 1 := by
  have key : ∀ (w : InfinitePlace E) i j, ((evGL w y).valᴴ * (evGL w y).val) i j = (y.valᴴ * y.val) i j w := by
    intro w i j
    simp [evGL, Matrix.mul_apply, Finset.sum_apply]
  constructor
  · intro h w
    ext i j
    rw [key, h]
    rcases eq_or_ne i j with rfl | e <;> simp [*]
  · intro h
    ext i j w
    rw [← key, h w]
    rcases eq_or_ne i j with rfl | e <;> simp [*]

theorem cInf_unitary (g : UA E n) : (cInf g).valᴴ * (cInf g).val = 1 := by
  have hg : cT (conjAd E) g.1.val * 1 * g.1.val = 1 := g.2
  rw [mul_one] at hg
  have h1 : (cInf g).val = g.1.val.map (pInf E) := rfl
  have h3 : (cT (conjAd E) g.1.val).map (pInf E) = (cInf g).valᴴ := by
    ext1 i j
    rw [Matrix.conjTranspose_apply, h1]
    exact (infEq E).symm_apply_apply _
  have h5 := congrArg (fun m => m.map (pInf E)) hg
  simp only [Matrix.map_mul, h3, ← h1] at h5
  rw [h5]
  ext1 i j
  rcases eq_or_ne i j with rfl | e <;> simp [*]

theorem continuous_pInfComp : Continuous (pInf E) := by
  have h : Continuous (infEq E).symm := continuous_pi fun w =>
    (InfinitePlace.Completion.isometryEquivComplexOfIsComplex (IsTotallyComplex.isComplex w)).continuous.comp
      (continuous_apply w)
  exact h.comp continuous_fst

theorem continuous_cInf : Continuous (cInf : UA E n → GL (Fin n) (Cinf E)) :=
  (Continuous.units_map _ (continuous_id.matrix_map continuous_pInfComp)).comp continuous_subtype_val

theorem continuous_cutGL (v : InfinitePlace E) : Continuous (cutGL v : GL (Fin n) (Cinf E) → _) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (atPlace v : Cinf E → Cinf E) :=
    continuous_pi fun w => by
      by_cases h : w = v
      · subst h
        exact (show Continuous fun x : Cinf E => x w from continuous_apply w).congr
          fun x => (atPlace_self w x).symm
      · exact continuous_const.congr fun x => (atPlace_of_ne h x).symm
  exact continuous_const.sub (continuous_const) |>.add (continuous_id.matrix_map hs)

theorem continuous_infGL : Continuous (infGL E n) := by
  refine Continuous.units_map _ ?_
  have hs : Continuous (sInf E : Cinf E → Ad E) :=
    (continuous_infEq E).prodMk continuous_const
  exact continuous_const.sub (continuous_const) |>.add (continuous_id.matrix_map hs)

theorem coord_embedding (w : InfinitePlace E) : coord w.embedding = Pi.evalRingHom (fun _ => ℂ) w := by
  have h := InfinitePlace.mk_embedding w
  unfold coord
  rw [if_pos (by rw [h]), h]

theorem map_coord_of_evGL (τ : E →+* ℂ) {y : GL (Fin n) (Cinf E)} (h : evGL (InfinitePlace.mk τ) y = 1) :
    GeneralLinearGroup.map (coord τ) y = 1 := by
  unfold coord
  split_ifs
  · exact h
  · have : GeneralLinearGroup.map ((starRingEnd ℂ).comp (Pi.evalRingHom (fun _ => ℂ) (InfinitePlace.mk τ))) y =
        GeneralLinearGroup.map (starRingEnd ℂ) (evGL (InfinitePlace.mk τ) y) := by
      ext i j
      rfl
    rw [this, h, map_one]

theorem evGL_cInf_of_mem {τ : E →+* ℂ} {x : UA E n} (hx : x ∈ embU n τ) {w : InfinitePlace E}
    (h : w ≠ InfinitePlace.mk τ) : evGL w (cInf x) = 1 := by
  have h1 : x ∈ (cEmb (n := n) w.embedding).ker :=
    Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 hx.2 w.embedding) (by rwa [InfinitePlace.mk_embedding])
  have h2 : GeneralLinearGroup.map (coord w.embedding) (cInf x) = 1 := MonoidHom.mem_ker.1 h1
  rwa [coord_embedding] at h2

def cutGA (τ : E →+* ℂ) : UA E n →* GA E n := (infGL E n).comp ((cutGL (InfinitePlace.mk τ)).comp cInf)

theorem cutGA_mem_UA (τ : E →+* ℂ) (g : UA E n) : cutGA τ g ∈ UA E n := by
  refine infGL_mem_UA (cutGL (InfinitePlace.mk τ) (cInf g)) ((unitary_iff_evGL _).2 fun w => ?_)
  by_cases h : w = InfinitePlace.mk τ
  · subst h
    rw [evGL_cutGL_self]
    exact (unitary_iff_evGL _).1 (cInf_unitary g) _
  · rw [evGL_cutGL_of_ne h]
    simp

theorem cInf_cutGA (τ : E →+* ℂ) (g : UA E n) :
    cInf (⟨cutGA τ g, cutGA_mem_UA τ g⟩ : UA E n) = cutGL (InfinitePlace.mk τ) (cInf g) :=
  pInf_infGL _

theorem cutGA_mem_embU (τ : E →+* ℂ) (g : UA E n) : (⟨cutGA τ g, cutGA_mem_UA τ g⟩ : UA E n) ∈ embU n τ := by
  refine ⟨pFin_infGL _, Subgroup.mem_iInf.2 fun τ' => Subgroup.mem_iInf.2 fun h => MonoidHom.mem_ker.2 ?_⟩
  change GeneralLinearGroup.map (coord τ') (cInf _) = 1
  rw [cInf_cutGA]
  exact map_coord_of_evGL τ' (evGL_cutGL_of_ne h _)

def embRet (τ : E →+* ℂ) : UA E n →* embU n τ where
  toFun g := ⟨⟨cutGA τ g, cutGA_mem_UA τ g⟩, cutGA_mem_embU τ g⟩
  map_one' := Subtype.ext (Subtype.ext (map_one (cutGA τ)))
  map_mul' a b := Subtype.ext (Subtype.ext (map_mul (cutGA τ) a b))

theorem cInf_embRet (τ : E →+* ℂ) (g : UA E n) :
    cInf (embRet τ g : UA E n) = cutGL (InfinitePlace.mk τ) (cInf g) := cInf_cutGA τ g

theorem continuous_embRet (τ : E →+* ℂ) : Continuous (embRet (n := n) τ) :=
  Continuous.subtype_mk (Continuous.subtype_mk
    (continuous_infGL.comp ((continuous_cutGL _).comp continuous_cInf)) _) _

theorem embRet_apply (τ : E →+* ℂ) (x : embU n τ) : embRet τ (x : UA E n) = x := by
  refine Subtype.ext (Subtype.ext (ga_ext ?_ ?_))
  · refine (cInf_embRet τ x.1).trans (gl_ext_evGL fun w => ?_)
    by_cases h : w = InfinitePlace.mk τ
    · subst h
      exact evGL_cutGL_self _ _
    · rw [evGL_cutGL_of_ne h]
      exact (evGL_cInf_of_mem x.2 h).symm
  · exact (pFin_infGL _).trans (MonoidHom.mem_ker.1 x.2.1).symm

theorem commute_embRet (τ : E →+* ℂ) (g : UA E n) (y : embU n τ) :
    Commute ((embRet τ g : UA E n)⁻¹ * g) (y : UA E n) := by
  have h2 : GeneralLinearGroup.map (pFin E) y.1.1 = 1 := y.2.1
  have h1 : evGL (InfinitePlace.mk τ) (cInf ((embRet τ g : UA E n)⁻¹ * g)) = 1 := by
    rw [map_mul, map_inv, cInf_embRet, map_mul, map_inv, evGL_cutGL_self, inv_mul_cancel]
  generalize (embRet τ g : UA E n)⁻¹ * g = a at h1 ⊢
  refine Subtype.ext (ga_ext ?_ ?_)
  · change cInf (a * y.1) = cInf (y.1 * a)
    rw [map_mul, map_mul]
    refine gl_ext_evGL fun w => ?_
    rw [map_mul, map_mul]
    by_cases h : w = InfinitePlace.mk τ
    · subst h
      rw [h1, one_mul, mul_one]
    · rw [evGL_cInf_of_mem y.2 h, one_mul, mul_one]
  · simp only [Subgroup.coe_mul, map_mul, h2, one_mul, mul_one]

theorem exists_embRet : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (τ : E →+* ℂ),
    ∃ r : UA E n →* embU n τ, Continuous r ∧ (∀ x : embU n τ, r x = x) ∧
      ∀ (g : UA E n) (y : embU n τ), Commute ((r g : UA E n)⁻¹ * g) (y : UA E n) :=
  fun _ _ _ _ _ τ => ⟨embRet τ, continuous_embRet τ, embRet_apply τ, commute_embRet τ⟩

end GlobalTheory.DefU

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsContinuousRetractionOntoUnitaryLocalPoints
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

noncomputable section

namespace GlobalTheory.DefU.LocRet

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem under_conjSrc (v : HeightOneSpectrum (𝓞 E)) :
    (conjSrc (IsCMField.complexConj E).toRingEquiv v).under (𝓞 (maximalRealSubfield E)) =
      v.under (𝓞 (maximalRealSubfield E)) := by
  have h := conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv v
  ext y
  change algebraMap _ (𝓞 E) y ∈ (conjSrc (IsCMField.complexConj E).toRingEquiv v).asIdeal ↔ algebraMap _ (𝓞 E) y ∈ v.asIdeal
  rw [← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← HeightOneSpectrum.valuation_lt_one_iff_mem (K := E), ← h]
  have : (IsCMField.complexConj E).toRingEquiv ((algebraMap _ (𝓞 E) y : 𝓞 E) : E) = ((algebraMap _ (𝓞 E) y : 𝓞 E) : E) := by
    change (IsCMField.complexConj E) (algebraMap (maximalRealSubfield E) E (y : maximalRealSubfield E)) = _
    rw [AlgEquiv.commutes]
    rfl
  rw [this]

variable (w : HeightOneSpectrum (𝓞 E))


open Classical in
def idemF : Af E :=
  ⟨fun v => if v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E)) then 1 else 0,
    Filter.Eventually.of_forall fun v => by
      dsimp only
      split_ifs
      · exact one_mem _
      · exact zero_mem _⟩

def idem : Ad E := sFin E (idemF w)

theorem idem_mul_idem : idem w * idem w = idem w := by
  refine Prod.ext (mul_zero _) (FiniteAdeleRing.ext E fun v => ?_)
  change (idemF w).1 v * (idemF w).1 v = (idemF w).1 v
  simp only [idemF]
  split_ifs <;> simp

def sIdem : Ad E →ₙ+* Ad E where
  toFun x := idem w * x
  map_mul' x y := by
    calc idem w * (x * y) = (idem w * idem w) * (x * y) := by rw [idem_mul_idem]
      _ = idem w * x * (idem w * y) := by ring
  map_zero' := mul_zero _
  map_add' x y := mul_add _ _ _

theorem pInf_sIdem (x : Ad E) : pInf E (sIdem w x) = 0 := by
  change pInf E (sFin E (idemF w) * x) = 0
  rw [map_mul]
  have : pInf E (sFin E (idemF w)) = 0 := map_zero (infEq E).symm
  rw [this, zero_mul]

theorem pLoc_sIdem_of_eq {v : HeightOneSpectrum (𝓞 E)}
    (hv : v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) (x : Ad E) :
    ((pLoc E v).comp (pFin E)) (sIdem w x) = ((pLoc E v).comp (pFin E)) x := by
  change ((pLoc E v).comp (pFin E)) (idem w) * _ = _
  have : ((pLoc E v).comp (pFin E)) (idem w) = 1 := by
    change (idemF w).1 v = 1
    simp only [idemF, if_pos hv]
  rw [this, one_mul]
  rfl

theorem pLoc_sIdem_of_ne {v : HeightOneSpectrum (𝓞 E)}
    (hv : v.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E))) (x : Ad E) :
    ((pLoc E v).comp (pFin E)) (sIdem w x) = 0 := by
  change ((pLoc E v).comp (pFin E)) (idem w) * _ = _
  have : ((pLoc E v).comp (pFin E)) (idem w) = 0 := by
    change (idemF w).1 v = 0
    simp only [idemF, if_neg hv]
  rw [this, zero_mul]

theorem conjAd_idem : conjAd E (idem w) = idem w := by
  refine Prod.ext ?_ (FiniteAdeleRing.ext E fun v => ?_)
  · change (infEq E) ((starRingEnd (Cinf E)) ((infEq E).symm 0)) = 0
    simp
  change pLoc E v (conjFin (IsCMField.complexConj E).toRingEquiv (idemF w)) = (idemF w).1 v
  rw [pLoc_conjFin]
  change conjLoc _ v ((idemF w).1 _) = (idemF w).1 v
  have hc := under_conjSrc (E := E) v
  simp only [idemF]
  split_ifs with h1 h2 h2
  · simp
  · exact absurd (hc.symm.trans h1) h2
  · exact absurd (hc.trans h2) h1
  · simp

variable {w} {n : ℕ}

theorem ga_ext' {g h : GA E n} (h1 : GeneralLinearGroup.map (pInf E) g = GeneralLinearGroup.map (pInf E) h)
    (h2 : ∀ v : HeightOneSpectrum (𝓞 E), GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) g =
      GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) h) : g = h := by
  refine ga_ext h1 (Units.ext (Matrix.ext fun i j => FiniteAdeleRing.ext E fun v => ?_))
  exact congrArg (fun x : GL (Fin n) (v.adicCompletion E) => x.val i j) (h2 v)

theorem cT_corner (M : Matrix (Fin n) (Fin n) (Ad E)) :
    cT (conjAd E) (corner (matN n (sIdem w)) M) = corner (matN n (sIdem w)) (cT (conjAd E) M) := by
  ext i j
  change conjAd E ((1 : Matrix (Fin n) (Fin n) (Ad E)) j i - idem w * (1 : Matrix (Fin n) (Fin n) (Ad E)) j i +
      idem w * M j i) = (1 : Matrix (Fin n) (Fin n) (Ad E)) i j - idem w * (1 : Matrix (Fin n) (Fin n) (Ad E)) i j +
      idem w * conjAd E (M j i)
  rw [map_add (f := _), map_sub, map_mul, map_mul, conjAd_idem, Matrix.one_apply, Matrix.one_apply]
  by_cases h : j = i
  · subst h; simp
  · simp [h, Ne.symm h]

theorem corner_mem (g : UA E n) : cornerGL n (sIdem w) g.1 ∈ UA E n := by
  have hg : cT (conjAd E) (g.1 : Matrix (Fin n) (Fin n) (Ad E)) * 1 * g.1 = 1 := g.2
  change cT (conjAd E) (corner (matN n (sIdem w)) g.1.1) * 1 * corner (matN n (sIdem w)) g.1.1 = 1
  rw [cT_corner, Matrix.mul_one, ← map_mul, ← Matrix.mul_one (cT (conjAd E) _), hg, map_one]


variable (n w) in
def ret0 : UA E n →* UA E n := ((cornerGL n (sIdem w)).comp (UA E n).subtype).codRestrict (UA E n) corner_mem

theorem infiniteProj_unitaryAdelicLocalRetractionEnd_eq_one (g : UA E n) : GeneralLinearGroup.map (pInf E) (ret0 w n g).1 = 1 :=
  map_cornerGL_of_zero _ _ (pInf_sIdem w) _

theorem localProj_unitaryAdelicLocalRetractionEnd_of_under_eq {v : HeightOneSpectrum (𝓞 E)}
    (hv : v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))) (g : UA E n) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (ret0 w n g).1 = GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) g.1 :=
  map_cornerGL_of_hom _ _ _ (pLoc_sIdem_of_eq w hv) _

theorem localProj_unitaryAdelicLocalRetractionEnd_of_under_ne {v : HeightOneSpectrum (𝓞 E)}
    (hv : v.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E))) (g : UA E n) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (ret0 w n g).1 = 1 :=
  map_cornerGL_of_zero _ _ (pLoc_sIdem_of_ne w hv) _

theorem unitaryAdelicLocalRetractionEnd_mem_localPoints (g : UA E n) : ret0 w n g ∈ locU n w := by
  refine Subgroup.mem_inf.2 ⟨MonoidHom.mem_ker.2 (infiniteProj_unitaryAdelicLocalRetractionEnd_eq_one g), Subgroup.mem_iInf.2 fun u => Subgroup.mem_iInf.2 fun hu => ?_⟩
  exact MonoidHom.mem_ker.2 (localProj_unitaryAdelicLocalRetractionEnd_of_under_ne hu g)

theorem mem_locU_inf {x : UA E n} (hx : x ∈ locU n w) : GeneralLinearGroup.map (pInf E) x.1 = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_inf.1 hx).1

theorem mem_locU_ne {x : UA E n} (hx : x ∈ locU n w) {v : HeightOneSpectrum (𝓞 E)}
    (hv : v.under (𝓞 (maximalRealSubfield E)) ≠ w.under (𝓞 (maximalRealSubfield E))) :
    GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) x.1 = 1 :=
  MonoidHom.mem_ker.1 (Subgroup.mem_iInf.1 (Subgroup.mem_iInf.1 (Subgroup.mem_inf.1 hx).2 v) hv)


variable (n w) in
def ret : UA E n →* locU n w := (ret0 w n).codRestrict (locU n w) unitaryAdelicLocalRetractionEnd_mem_localPoints

theorem continuous_ret : Continuous (ret w n) := by
  have hc : Continuous (corner (matN n (sIdem w))) := by
    change Continuous fun M : Matrix (Fin n) (Fin n) (Ad E) => 1 - (1 : Matrix (Fin n) (Fin n) (Ad E)).map (idem w * ·) +
      M.map (idem w * ·)
    exact continuous_const.add (continuous_id.matrix_map (continuous_const.mul continuous_id))
  exact Continuous.subtype_mk (Continuous.subtype_mk ((Continuous.units_map _ hc).comp continuous_subtype_val) _) _

theorem ret_of_mem (x : locU n w) : ret w n x = x := by
  refine Subtype.ext (Subtype.ext (ga_ext' ?_ fun v => ?_))
  · exact (infiniteProj_unitaryAdelicLocalRetractionEnd_eq_one x.1).trans (mem_locU_inf x.2).symm
  · by_cases hv : v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))
    · exact localProj_unitaryAdelicLocalRetractionEnd_of_under_eq hv x.1
    · exact (localProj_unitaryAdelicLocalRetractionEnd_of_under_ne hv x.1).trans (mem_locU_ne x.2 hv).symm

theorem commute_ret (g : UA E n) (y : locU n w) : Commute ((ret w n g : UA E n)⁻¹ * g) (y : UA E n) := by
  refine Subtype.ext (ga_ext' ?_ fun v => ?_)
  · simp only [Subgroup.coe_mul, map_mul, mem_locU_inf y.2, one_mul, mul_one]
  · by_cases hv : v.under (𝓞 (maximalRealSubfield E)) = w.under (𝓞 (maximalRealSubfield E))
    · have h : GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (((ret w n g : UA E n)⁻¹ * g : UA E n) : GA E n) = 1 := by
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv]
        change (GeneralLinearGroup.map ((pLoc E v).comp (pFin E)) (ret0 w n g).1)⁻¹ * _ = 1
        rw [localProj_unitaryAdelicLocalRetractionEnd_of_under_eq hv g, inv_mul_cancel]
      simp only [Subgroup.coe_mul, map_mul] at h ⊢
      rw [h, one_mul, mul_one]
    · simp only [Subgroup.coe_mul, map_mul, mem_locU_ne y.2 hv, one_mul, mul_one]

theorem exists_ret (E : Type) [Field E] [NumberField E] [IsCMField E] (n : ℕ) (w : HeightOneSpectrum (𝓞 E)) :
    ∃ r : UA E n →* locU n w, Continuous r ∧ (∀ x : locU n w, r x = x) ∧
      ∀ (g : UA E n) (y : locU n w), Commute ((r g : UA E n)⁻¹ * g) (y : UA E n) :=
  ⟨ret w n, continuous_ret, ret_of_mem, commute_ret⟩

end GlobalTheory.DefU.LocRet

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMultilinearMapOfCommutingEndAlgHom
section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC Formalism.UG Formalism.BasicNotions GlobalTheory.DefU

namespace GlobalTheory

theorem exists_multilinear_of_commuting_endAlgHom :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Wv : ι → Type) [∀ v, AddCommGroup (Wv v)]
      [∀ v, Module ℂ (Wv v)] (V : Type) [AddCommGroup V] [Module ℂ V]
      (Φ : ∀ v, Module.End ℂ (Wv v) →ₐ[ℂ] Module.End ℂ V) (w : ∀ v, Wv v)
      (ℓ : ∀ v, Module.Dual ℂ (Wv v)) (y : V),
      (∀ u v, u ≠ v → ∀ A B, Commute (Φ u A) (Φ v B)) →
      (∀ v, Φ v ((ℓ v).smulRight (w v)) y = y) →
      ∃ F : (∀ v, Wv v) →ₘₗ[ℂ] V, F w = y ∧
        ∀ v (A : Module.End ℂ (Wv v)) (x : ∀ u, Wv u),
          Φ v A (F x) = F (Function.update x v (A (x v))) := by
  intro ι _ hd Wv _ _ V _ _ Φ w ℓ y hc hfix
  let f : (∀ v, Wv v) → ι → Module.End ℂ V := fun x v => Φ v ((ℓ v).smulRight (x v))
  have comm : ∀ x, ((Finset.univ : Finset ι) : Set ι).Pairwise (Function.onFun Commute (f x)) :=
    fun x a _ b _ hab => hc a b hab _ _
  let G : (∀ v, Wv v) → V := fun x => (Finset.univ.noncommProd (f x) (comm x)) y

  let R : (∀ v, Wv v) → ι → Module.End ℂ V := fun x v =>
    (Finset.univ.erase v).noncommProd (f x)
      (fun _ ha _ hb hab => comm x (Finset.mem_of_mem_erase ha) (Finset.mem_of_mem_erase hb) hab)
  have hsplit : ∀ x v, G x = f x v (R x v y) := by
    intro x v
    simp only [G, R]
    rw [← Finset.mul_noncommProd_erase Finset.univ (Finset.mem_univ v) (f x) (comm x)]
    rfl
  have hR : ∀ x v (a : Wv v), R (Function.update x v a) v = R x v := by
    intro x v a
    simp only [R]
    apply Finset.noncommProd_congr rfl
    intro u hu
    simp only [f, Function.update_of_ne (Finset.ne_of_mem_erase hu)]
  have hfu : ∀ x v (a : Wv v), f (Function.update x v a) v = Φ v ((ℓ v).smulRight a) := by
    intro x v a
    simp only [f, Function.update_self]
  refine ⟨{ toFun := G, map_update_add' := ?_, map_update_smul' := ?_ }, ?_, ?_⟩
  · intro dec x v a b
    obtain rfl : dec = hd := Subsingleton.elim _ _
    have e : (ℓ v).smulRight (a + b) = (ℓ v).smulRight a + (ℓ v).smulRight b := by
      ext z; simp [smul_add]
    rw [hsplit _ v, hsplit _ v, hsplit _ v, hR, hR, hR, hfu, hfu, hfu, e, map_add (f := _),
      LinearMap.add_apply]
  · intro dec x v c a
    obtain rfl : dec = hd := Subsingleton.elim _ _
    simp only [RingHom.id_apply]
    have e : (ℓ v).smulRight (c • a) = c • (ℓ v).smulRight a := by
      ext z; simp [smul_comm c]
    rw [hsplit _ v, hsplit _ v, hR, hR, hfu, hfu, e, map_smul, LinearMap.smul_apply]
  · show (Finset.univ.noncommProd (f w) (comm w)) y = y
    exact Finset.noncommProd_induction _ _ _ (fun T : Module.End ℂ V => T y = y)
      (fun S T hS hT => by rw [mul_apply_eq_comp, hT, hS]) rfl
      (fun v _ => hfix v)
  · intro v A x
    show Φ v A (G x) = G (Function.update x v (A (x v)))
    rw [hsplit x v, hsplit _ v, hR, hfu]
    have : (ℓ v).smulRight (A (x v)) = A * (ℓ v).smulRight (x v) := by
      ext z; simp
    rw [this, map_mul, mul_apply_eq_comp]

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsClosedDerivativeFamiliesModerateGrowthStatement
section
open MeasureTheory Matrix Filter Formalism.REAL Formalism.MainNotions.S Formalism.L2.Theta GlobalTheory.SmoothGlob GlobalTheory.LowTypeDetermined GlobalTheory.TypeSum
open scoped InnerProductSpace Topology
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isClosed_derivativeFamilies_moderateGrowth : ∀ (n : ℕ) (ε : Fin n → Bool) (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] (ρ : Mx n → (E →L[ℂ] E)), ModRep ε ρ → IsClosed (Fam ε ρ : Set (List (lie (Jm ε)) → E)) := by
  first | exact @GlobalTheory.TypeSum.isClosed_fam | exact GlobalTheory.TypeSum.isClosed_fam | (intros; apply GlobalTheory.TypeSum.isClosed_fam <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSmoothAutomorphicFunctionTranslateAtRealPlaceStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta GlobalTheory.Mem.Th MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isSmoothAutomorphicFunction_translate_atRealPlace : ∀ (D : D7) (θ : InfF D), IsInfFam θ → ∀ (V : HSp D) (φ : GA D V → ℂ), IsAutFunSm θ V φ → ∀ τ, ∀ g ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ), IsAutFunSm θ V (rTr V (atTau θ V τ g) φ) := by
  first | exact @GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau | exact GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau | (intros; apply GlobalTheory.Mem.RealTranslate.isAutFunSm_rTr_atTau <;> assumption)
end

