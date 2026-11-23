module

public import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.Bundle0002
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentForm
public import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.SiegelWeilMeasureOfCongruentTarget

@[expose] public section

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.IsomC
section
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.SWIsom
open scoped TensorProduct ENNReal NNReal Matrix

theorem isomC : IsomC := by
  intro F E _ _ _ _ _ σ hCM M J hJ g J' hJ'eq n T hT _ hSW
  subst hJ'eq
  have hJ' := isHermND_conj σ hCM J hJ g
  intro d b laminf lam hinf hlam μ 𝓕 hμ h𝓕 minf m hminf hm
  obtain ⟨⟨i1, i2, i3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  haveI := i1
  haveI := i2
  haveI := i3
  obtain ⟨e, hmat, hrat⟩ := GlobalTheory.CompanionTheory.SW.HIsom.unitaryIsom_of_isometry F E σ hCM M J hJ g _ rfl (AF F)
  obtain ⟨tg, -, -, -, bs, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hCM M J hJ (AF F)
  obtain ⟨tg', -, -, -, bs', -⟩ := _root_.GlobalTheory.CompanionTheory.SW.TopH.topH_props F E σ hCM M _ hJ' (AF F)
  haveI := tg
  haveI := tg'
  haveI := bs
  haveI := bs'
  haveI : μ.IsHaarMeasure := hμ
  let He := e.toHomeomorph.toMeasurableEquiv
  have hμ' : IsHaarH F E σ M _ (μ.map He.symm) := ContinuousMulEquiv.isHaarMeasure_map μ e.symm
  have hmm : (μ.map He.symm).map He = μ := by
    rw [Measure.map_map He.measurable He.symm.measurable]
    simp
  have hq : Measure.QuasiMeasurePreserving e (μ.map He.symm) μ :=
    (MeasurePreserving.mk He.measurable hmm).quasiMeasurePreserving
  have h𝓕' : IsFDH F E σ M _ (μ.map He.symm) (He ⁻¹' 𝓕) :=
    isFD_pull σ e.toMulEquiv hrat hq h𝓕
  have hLi : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
  have hLv : ∀ v, IsLocR (Fv F v) := fun v => GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F v
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  have hWi := haar_of_loc σ hCM (Ainf F) hLi b laminf hinf.1 n M
  have hWv := fun v => haar_of_loc σ hCM (Fv F v) (hLv v) b (lam v) (hlam v).1 n M
  obtain ⟨minf', hminf'⟩ := _root_.GlobalTheory.CompanionTheory.SW.GramExist.exists_gramFib F E σ hCM M _ hJ' (Ainf F) hLi n _ _ hWi.1 hWi.2
  choose m' hm' using fun v =>
    _root_.GlobalTheory.CompanionTheory.SW.GramExist.exists_gramFib F E σ hCM M _ hJ' (Fv F v) (hLv v) n _ _ (hWv v).1 (hWv v).2
  obtain ⟨cinf, c, hUP, hci, hcv⟩ := _root_.GlobalTheory.CompanionTheory.SW.PfAct.product_formula_actTup F E σ hCM n M g
  obtain ⟨κ, hEul, hκ⟩ := hSW d b laminf lam hinf hlam (μ.map He.symm) (He ⁻¹' 𝓕) hμ' h𝓕' minf' m' hminf' hm'
  refine ⟨κ, ?_, hκ⟩
  have hfin : ∀ v, (cfac E v • m v (hermOf (Fv F v) σ T hT)) (latV b v) < ⊤ := by
    intro v
    haveI := (_root_.GlobalTheory.CompanionTheory.SW.LocFin.fibre_loc_fin F E σ hCM M J hJ (Fv F v) (hLv v) n _ _ (m v) (hWv v).1 (hWv v).2 (hm v)
      (hermOf (Fv F v) σ T hT)).1
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top
      ((_root_.GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hCM d b n M).2.2.2.1 v).1.measure_lt_top
  have hproj : ∀ X : Fin n → Fin M → AF F ⊗[F] E,
      projInf (actTup (AF F) (bc (inclR (AF F)) g) X) =
          actTup (Ainf F) (bc (inclR (Ainf F)) g) (projInf X) ∧
        ∀ v, projV v (projFin (actTup (AF F) (bc (inclR (AF F)) g) X)) =
          actTup (Fv F v) (bc (inclR (Fv F v)) g) (projV v (projFin X)) := by
    intro X
    refine ⟨?_, fun v => ?_⟩
    · funext a i
      exact map_actTup (fstA F) g X a i
    · have h1 : projFin (actTup (AF F) (bc (inclR (AF F)) g) X) =
          actTup (Af F) (bc (inclR (Af F)) g) (projFin X) := by
        funext a i
        exact map_actTup (sndA F) g X a i
      rw [h1]
      funext a i
      exact map_actTup (evalV F v) g (projFin X) a i
  have hlocI := local_map σ hCM J hJ g (Ainf F) hLi n _ _ hWi.1 hWi.2 minf minf' hminf hminf' cinf
    (hci _ hWi.1) (hermOf (Ainf F) σ T hT)
  have hlocV := fun v => local_map σ hCM J hJ g (Fv F v) (hLv v) n _ _ (hWv v).1 (hWv v).2 (m v) (m' v) (hm v)
      (hm' v) (c v) (hcv v _ (hWv v).1) (hermOf (Fv F v) σ T hT)
  have key := _root_.GlobalTheory.CompanionTheory.SW.EulerMove.euler_move F E σ hCM d b n M _ (κ • minf' (hermOf (Ainf F) σ T hT))
    (κ • minf (hermOf (Ainf F) σ T hT)) (fun v => cfac E v • m' v (hermOf (Fv F v) σ T hT))
    (fun v => cfac E v • m v (hermOf (Fv F v) σ T hT)) (actTup (AF F) (bc (inclR (AF F)) g))
    (actTup (Ainf F) (bc (inclR (Ainf F)) g)) (fun v => actTup (Fv F v) (bc (inclR (Fv F v)) g))
    (measurable_actTup σ hCM (AF F) _) (measurable_of_loc σ hCM (Ainf F) hLi _)
    (fun v => measurable_of_loc σ hCM (Fv F v) (hLv v) _) hproj
    ((GlobalTheory.CompanionTheory.SW.LatRat.latV_rational F E σ hCM d b n M).2.1 g) cinf c hUP
    (by
      rw [Measure.map_smul, hlocI, smul_comm]
      exact (measurable_of_loc σ hCM (Ainf F) hLi _).aemeasurable)
    (fun v => by
      rw [Measure.map_smul, hlocV v, smul_comm]
      exact (measurable_of_loc σ hCM (Fv F v) (hLv v) _).aemeasurable) hfin
    ((isEulerProd_const_iff b _ κ _ _).1 hEul)
  have hth := theta_map (n := n) σ hCM J hJ g He hmat μ 𝓕 T
  rw [hth] at key
  exact (isEulerProd_const_iff b _ κ _ _).2 key

end PositivityTheory.SiegelWeilFormula.Densx

end
end

-- bundled from Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.ScaleC
section
noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.Scale
open scoped TensorProduct ENNReal NNReal Matrix

theorem scaleC : ScaleC := by
  intro F E _ _ _ _ _ σ hcm M J hJ n T hT _ g T' hT' hrel hSW d b laminf lam hinf hv μ 𝓕 hH hF minf m
    hminf hm
  have hinv := (HaarCoord.conj_facts hcm).1
  obtain ⟨G, hG⟩ : ∃ G : Matrix (Fin n) (Fin n) E, G = (g : Matrix (Fin n) (Fin n) E) := ⟨_, rfl⟩
  obtain ⟨H, hHd⟩ : ∃ H : Matrix (Fin n) (Fin n) E, H = ((g⁻¹ : GL (Fin n) E) : Matrix (Fin n) (Fin n) E) :=
    ⟨_, rfl⟩
  have hGH : G * H = 1 := by rw [hG, hHd]; exact Units.mul_inv g
  have hHG : H * G = 1 := by rw [hG, hHd]; exact Units.inv_mul g
  rw [← hG] at hrel
  have hdetH : H.det ≠ 0 := by
    intro h0
    have : H.det * G.det = 1 := by rw [← Matrix.det_mul, hHG, Matrix.det_one]
    rw [h0, zero_mul] at this
    exact zero_ne_one this
  have hrel' : cT (σ : E →+* E) H * T' * H = T := by
    rw [hrel]
    calc cT (σ : E →+* E) H * (cT (σ : E →+* E) G * T * G) * H
        = (cT (σ : E →+* E) H * cT (σ : E →+* E) G) * T * (G * H) := by
          simp only [Matrix.mul_assoc]
      _ = T := by rw [← cT_mul, hGH, cT_one, Matrix.one_mul, Matrix.mul_one]
  obtain ⟨ai, a, hau, hai, hav⟩ := _root_.GlobalTheory.CompanionTheory.SW.RmulPF.rmul_product_formula F E σ hcm n M H hdetH
  obtain ⟨ci, c, hcu, hci, hcv⟩ := _root_.GlobalTheory.CompanionTheory.SW.pf_herm F E σ hcm n H hdetH
  obtain ⟨-, -, -, -, hq, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.UnitProdAlg.main F ai ci a c hau hcu
  obtain ⟨hci0, hc0, -⟩ := _root_.GlobalTheory.CompanionTheory.SW.UnitProdAlg.main F ci ai c a hcu hau
  have hrI : IsLocR (Ainf F) := isLocR_Ainf F hcm.1
  have hrV : ∀ v, IsLocR (Fv F v) := fun v => LocFv.isLocR_Fv F v
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v, BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  have sInf := unitary_conjugate_local σ hcm hinv J hJ (Ainf F) hrI b laminf hinf.1 minf hminf H T T' hdetH hT hT'
    hrel' ai ci hci0 hai hci
  have sV := fun v => unitary_conjugate_local σ hcm hinv J hJ (Fv F v) (hrV v) b (lam v) (hv v).1 (m v) (hm v) H T T'
    hdetH hT hT' hrel' (a v) (c v) (hc0 v) (hav v) (hcv v)
  obtain ⟨⟨t1, t2, t3⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  have me := measurable_rmul σ hcm (AF F) n M (H.map (inclR (F := F) (AF F)))
  have mi : Measurable fun X : Fin n → Fin M → Ainf F ⊗[F] E =>
      rmul (Ainf F) X (H.map (inclR (F := F) (Ainf F))) := by
    obtain ⟨r1, r2, r3, r4, -⟩ := hrI
    exact measurable_rmul σ hcm (Ainf F) n M _
  have mv : ∀ v, Measurable fun X : Fin n → Fin M → Fv F v ⊗[F] E =>
      rmul (Fv F v) X (H.map (inclR (F := F) (Fv F v))) := by
    intro v
    obtain ⟨r1, r2, r3, r4, -⟩ := hrV v
    exact measurable_rmul σ hcm (Fv F v) n M _
  obtain ⟨κ, hE, hκ⟩ := hSW d b laminf lam hinf hv μ 𝓕 hH hF minf m hminf hm
  refine ⟨κ, ?_, hκ⟩
  have hth := theta_map σ hcm J hJ μ 𝓕 hH hF G H T T' hGH hHG hrel' hrel.symm me
  have hlat := (_root_.GlobalTheory.CompanionTheory.SW.MeasProj.proj_props F E σ hcm d b n M).2.2.2
  have hfin : ∀ v, (cfac E v • m v (hermOf (Fv F v) σ T hT)) (latV b v) < ⊤ := by
    intro v
    obtain ⟨r1, r2, r3, r4, -⟩ := id (hrV v)
    obtain ⟨-, hW, hHm⟩ := coord_measures_haar F E σ hcm (Fv F v) d b (lam v) (hv v).1
    haveI := (_root_.GlobalTheory.CompanionTheory.SW.LocFin.fibre_loc_fin F E σ hcm M J hJ (Fv F v) (hrV v) n _ _ (m v) (hW n M) (hHm n) (hm v)
      (hermOf (Fv F v) σ T hT)).1
    rw [Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
    exact ENNReal.mul_lt_top ENNReal.coe_lt_top (hlat.1 v).1.measure_lt_top
  rw [isEulerProd_const_iff, ← hth]
  exact _root_.GlobalTheory.CompanionTheory.SW.EulerMove.euler_move F E σ hcm d b n M _ (κ • minf (hermOf (Ainf F) σ T' hT')) (κ • minf (hermOf (Ainf F) σ T hT))
    (fun v => cfac E v • m v (hermOf (Fv F v) σ T' hT')) (fun v => cfac E v • m v (hermOf (Fv F v) σ T hT))
    (fun X => rmul (AF F) X (H.map (inclR (F := F) (AF F))))
    (fun X => rmul (Ainf F) X (H.map (inclR (F := F) (Ainf F))))
    (fun v X => rmul (Fv F v) X (H.map (inclR (F := F) (Fv F v)))) me mi mv
    (fun X => ⟨projInf_rmul X H, fun v => projV_rmul v X H⟩)
    ((LatRat.latV_rational F E σ hcm d b n M).1 H hdetH)
    (ai / ci) (fun v => a v / c v) hq (by rw [Measure.map_smul, sInf, smul_comm]; exact mi.aemeasurable)
    (fun v => by rw [Measure.map_smul, sV v, smul_comm]; exact (mv v).aemeasurable) hfin
    ((isEulerProd_const_iff b _ κ _ _).1 hE)

end PositivityTheory.SiegelWeilFormula.Densx

end
end

