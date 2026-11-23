module

public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.KirillovFunctionValueEq
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.Bundle0006
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.Bundle0002
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.Bundle0001
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.Bundle0003
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.LocalLevelOutsideSigma
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsIntegralLf
public import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Bundle0003
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0004
public import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0005
public import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PadicIsNonarchimedeanLocalField
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0026
public import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup
public import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0460

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.SaNormal
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace UpperTheory.V.Z.Sym.So

private theorem dc_conj {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (S U : Subgroup G) (hS : S.Normal) (a : S) (y : G)
    (hy : y * (a : G) = a * y) (hfin : AlgebraTools.FinOrb U U (a : G))
    (hc : ∀ u ∈ U, ∃ c ∈ U, c * (a : G) = a * c ∧ u * c⁻¹ ∈ S ∧ c⁻¹ * u ∈ S)
    (φ : G → V) (hφ : ∀ u ∈ U, ∀ g, φ (g * u) = φ g) (g : S) :
    dcF ((U.comap (MulAut.conj y⁻¹).toMonoidHom).subgroupOf S) a (fun h : S => φ (h * y)) g = dcF U (a : G) φ (g * y) := by
  classical
  have hmem : ∀ u : G, u ∈ U.comap (MulAut.conj y⁻¹).toMonoidHom ↔ y⁻¹ * u * y ∈ U := by
    intro u
    simp [MulAut.conj_apply]
  have hea : (MulAut.conj y⁻¹).toMonoidHom (a : G) = a := by
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv]
    rw [mul_assoc, ← hy, inv_mul_cancel_left]
  have hbij : Function.Bijective (MulAut.conj y⁻¹).toMonoidHom := (MulAut.conj y⁻¹).bijective
  have hM := dcMap G G V (MulAut.conj y⁻¹).toMonoidHom hbij U (a : G) (a : G)
  rw [hea] at hM
  obtain ⟨-, hfinIff, -, hmap⟩ := hM
  have hfin' := hfinIff.2 hfin
  have hφy : ∀ u ∈ U, ∀ x : G, φ (y * (x * u)) = φ (y * x) := by
    intro u hu x
    rw [← mul_assoc]
    exact hφ u hu _
  have htr : ∀ z : G, dcF U (a : G) (fun x => φ (y * x)) z = dcF U (a : G) φ (y * z) := by
    intro z
    rw [(dcBasic G V U a hfin (fun x => φ (y * x)) hφy).2.1, (dcBasic G V U a hfin φ hφ).2.1]
    simp only [mul_assoc]
  have hA : ∀ x : G, dcF (U.comap (MulAut.conj y⁻¹).toMonoidHom) (a : G) (fun h => φ (h * y)) x
      = dcF U (a : G) φ (x * y) := by
    intro x
    have h1 := congrFun (hmap hfin (fun x => φ (y * x)) hφy) x
    have h2 : ((fun x => φ (y * x)) ∘ (MulAut.conj y⁻¹).toMonoidHom) = fun h => φ (h * y) := by
      funext h
      simp [MulAut.conj_apply, mul_assoc]
    rw [h2] at h1
    rw [h1]
    simp only [Function.comp_apply]
    rw [htr]
    simp [MulAut.conj_apply, mul_assoc]
  have hay : (a : G) * y⁻¹ = y⁻¹ * a := by
    rw [mul_inv_eq_iff_eq_mul, mul_assoc, ← hy, inv_mul_cancel_left]
  have hc' : ∀ u ∈ U.comap (MulAut.conj y⁻¹).toMonoidHom, ∃ c ∈ U.comap (MulAut.conj y⁻¹).toMonoidHom,
      c * (a : G) = a * c ∧ u * c⁻¹ ∈ S ∧ c⁻¹ * u ∈ S := by
    intro u hu
    obtain ⟨c, hcU, hca, h1, h2⟩ := hc _ ((hmem u).1 hu)
    refine ⟨y * c * y⁻¹, (hmem _).2 (by simpa [mul_assoc] using hcU), ?_, ?_, ?_⟩
    · calc y * c * y⁻¹ * (a : G) = y * c * (a * y⁻¹) := by rw [hay, mul_assoc]
        _ = y * (c * a) * y⁻¹ := by simp only [mul_assoc]
        _ = y * a * c * y⁻¹ := by rw [hca]; simp only [mul_assoc]
        _ = (a : G) * (y * c * y⁻¹) := by rw [hy]; simp only [mul_assoc]
    · have := hS.conj_mem _ h1 y
      simpa [mul_assoc] using this
    · have := hS.conj_mem _ h2 y
      simpa [mul_assoc] using this
  have hψG : ∀ u ∈ U.comap (MulAut.conj y⁻¹).toMonoidHom, ∀ x : G, φ (x * u * y) = φ (x * y) := by
    intro u hu x
    have := hφ _ ((hmem u).1 hu) (x * y)
    simpa [mul_assoc] using this
  obtain ⟨hfS, hDC, -, R, hR1, hR2, hR3⟩ := dcSub G V S _ a hfin' hc' hS
  have hψS : ∀ u ∈ (U.comap (MulAut.conj y⁻¹).toMonoidHom).subgroupOf S, ∀ x : S,
      φ (((x * u : S) : G) * y) = φ ((x : G) * y) := by
    intro u hu x
    rw [Subgroup.mem_subgroupOf] at hu
    simpa using hψG _ hu x
  rw [(dcBasic S V _ a hfS (fun h : S => φ (h * y)) hψS).2.2.2.2 R hR1 hR2 g, ← hA]
  rw [(dcBasic G V _ (a : G) hfin' (fun h => φ (h * y)) hψG).2.2.2.2 (R.map (Function.Embedding.subtype _)) ?_ ?_ g]
  · rw [Finset.sum_map]
    simp
  · intro z hz
    obtain ⟨r, hr, rfl⟩ := Finset.mem_map.1 hz
    exact (hDC r).1 (hR1 r hr)
  · intro z hz
    obtain ⟨r, ⟨hr, hrz⟩, huniq⟩ := hR3 z hz
    refine ⟨(r : G), ⟨Finset.mem_map_of_mem _ hr, hrz⟩, ?_⟩
    rintro w ⟨hw, hwz⟩
    obtain ⟨r', hr', rfl⟩ := Finset.mem_map.1 hw
    exact congrArg Subtype.val (huniq r' ⟨hr', hwz⟩)

private theorem sa_normal {F : Type} [Field F] [NumberField F] (Δ : F) : (SA Δ).Normal := by
  unfold SA
  refine Subgroup.normal_iInf_normal fun v => ?_
  have hN : (SU ((cv v) Δ)).Normal := by
    unfold SU
    exact MonoidHom.normal_ker _
  exact hN.comap _

end UpperTheory.V.Z.Sym.So

theorem UpperTheory.V.Z.Sym.So.kRes :
    UpperTheory.V.Z.Sym.So.KRes := by
  intro F _ _ Δ A hA V _ _ ch C hC y hy φ hφ a ha
  have hK := kOps F Δ A hA V ch C hC
  have hφU : ∀ u ∈ A.dat.U2, ∀ g : DA Δ, φ (g * u) = φ g := hK.2.1 φ hφ
  constructor
  · intro γ g g' hg
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype]
    rw [hg, mul_assoc]
    exact hφ.1 (γ : DX Δ) _
  · intro u hu g
    unfold SD.lvS at hu
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap] at hu
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, inv_inv] at hu
    have := hφU _ hu ((g : DA Δ) * y)
    simpa [mul_assoc] using this
  · intro t g hdom hel
    have hyc : y * (g : DA Δ) = (g : DA Δ) * y := by
      apply Subtype.ext
      funext v
      by_cases hv : v ∈ A.Sg
      · have h1 := hy v hv
        simp [h1]
      · have h1 := hel.2 v hv
        simp [h1]
    have hfin := (dMul F Δ A hA (g : DA Δ) (SD.dS t) hel).1
    have hc : ∀ u ∈ A.dat.U2, ∃ c ∈ A.dat.U2, c * (g : DA Δ) = g * c ∧ u * c⁻¹ ∈ SA Δ ∧ c⁻¹ * u ∈ SA Δ := by
      intro u hu
      obtain ⟨c, hcU, h1, h2, h3⟩ := torPart F Δ A hA u hu
      exact ⟨c, hcU, h3 _ _ hel, h1, h2⟩
    funext h
    rw [Pi.smul_apply]
    unfold SD.lvS
    rw [dc_conj (SA Δ) A.dat.U2 (sa_normal Δ) g y hyc hfin hc φ hφU h, ha t g hdom hel]
    rfl

end
end

-- bundled from Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GeneralizedEigenspaces.CharacterShapes.FiniteOrbits.SplitLoc
section
noncomputable section

open NumberField IsDedekindDomain ValuativeRel GlobalTheory.CuspRep GlobalTheory.PRep GlobalTheory.UnitaryBC GlobalTheory.SmGL Formalism.BasicNotions UpperTheory.V.Hi UpperTheory.V.AlgebraTools
open UpperTheory.V.W (Plc Lp)
open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.So UpperTheory.V.Z.Sym.Dict UpperTheory.V.Z.Sym.Dict.Br

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

section
open GlobalTheory.SplitWeil
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

private theorem split_loc (O : Type) [CommRing O] [Algebra O k] (hO : IsInts k O) (h2 : (2 : k) ≠ 0) {Δ s : k}
    (hs : s * s = Δ) (hs0 : s ≠ 0) (x : DX Δ) (hx : x ∈ KD Δ O) :
    ∃ t ∈ SU Δ, eD hs (t⁻¹ * x) ∈ (Lev.iw k).J 2 := by
  obtain ⟨hbij, hKO, -, -, hdet, -⟩ := eD_facts k O hO h2 Δ s hs hs0
  have hxK : eD hs x ∈ KO k (Fin 2) := by
    have hx' : x ∈ Subgroup.comap (eD hs) (KO k (Fin 2)) := by
      rw [hKO]
      exact hx
    exact hx'
  let d : Fin 2 → kˣ := ![Matrix.GeneralLinearGroup.det (eD hs x), 1]
  have hd : Matrix.GeneralLinearGroup.det (dg d) = Matrix.GeneralLinearGroup.det (eD hs x) := by
    apply Units.ext
    simp [dg, val_diagT, Matrix.det_diagonal, Fin.prod_univ_two, d]
  obtain ⟨t, ht⟩ := hbij.2 (eD hs x * (dg d)⁻¹)
  refine ⟨t, ?_, ?_⟩
  · rw [SU, MonoidHom.mem_ker]
    apply Units.ext
    simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, Matrix.GeneralLinearGroup.val_det_apply, Units.val_one]
    rw [show (↑(↑t : GL (Fin 2) (Lsq k Δ)) : Matrix (Fin 2) (Fin 2) (Lsq k Δ)) = Glob.mt t from rfl, (hdet t).1, ht,
      ← Matrix.GeneralLinearGroup.val_det_apply, map_mul, map_inv, hd, mul_inv_cancel, Units.val_one, map_one]
  · rw [map_mul, map_inv, ht, mul_inv_rev, inv_inv, inv_mul_cancel_right]
    apply Lev.dg_mem
    intro i
    fin_cases i
    · show valuation k (↑(Matrix.GeneralLinearGroup.det (eD hs x)) : k) = 1
      exact GlobalTheory.StepData.valuation_det_of_mem_KO hxK
    · exact one_mem _

end

private theorem eD_congr {K : Type} [Field K] {Δ s s' : K} (h : s * s = Δ) (h' : s' * s' = Δ) (e : s = s') (x : DX Δ) :
    eD h x = eD h' x := by
  subst e
  rfl

theorem UpperTheory.V.Z.Sym.So.kNon :
    UpperTheory.V.Z.Sym.So.KNon := by
  intro F _ _ Δ A hA A₀ hA₀ hE V _ _ ch C hC Y hY hoff φ hφ hφ0
  classical
  obtain ⟨-, -, hloc, -, hU2⟩ := datOk F Δ A hA
  obtain ⟨-, -, -, -, hU2₀⟩ := datOk F Δ A₀ hA₀
  have hinv := (kOps F Δ A hA V ch C hC).2.1 φ hφ
  obtain ⟨g, hg⟩ : ∃ g, φ g ≠ 0 := by
    by_contra h
    push_neg at h
    exact hφ0 (funext h)
  obtain ⟨γ, s, hs, y, hy, u, hu, rfl⟩ := hY.2 g
  have hu₀ := (hU2₀ u).1 hu
  have hspl : ∀ v (h : v ∈ A.Sg ∧ v ∉ A₀.Sg), ∃ r ∈ SU ((cv v) Δ),
      eD (A.hs v h.1) (r⁻¹ * u.1 v) ∈ (Lev.iw (Kv v)).J 2 := fun v h =>
    split_loc (Ov v) (hloc v h.1).1 (hloc v h.1).2.1 (A.hs v h.1) (hloc v h.1).2.2.1 (u.1 v) (hu₀.2 v h.2)
  let tf : (v : Pl F) → ↥(DX ((cv v) Δ)) := fun v =>
    if h : v ∈ A.Sg ∧ v ∉ A₀.Sg then (hspl v h).choose else 1
  have htf : tf ∈ RP (fun v => ↥(DX ((cv v) Δ))) (fun v => KD ((cv v) Δ) (Ov v)) := by
    show ∀ᶠ v in Filter.cofinite, tf v ∈ KD ((cv v) Δ) (Ov v)
    refine Filter.eventually_cofinite.mpr (A.Sg.finite_toSet.subset ?_)
    intro v hv
    by_contra h
    apply hv
    have hn : ¬ (v ∈ A.Sg ∧ v ∉ A₀.Sg) := fun h' => h h'.1
    simp only [tf, dif_neg hn]
    exact one_mem _
  let t : DA Δ := ⟨tf, htf⟩
  have hcomm : t * y = y * t := by
    apply Subtype.ext
    funext v
    show tf v * y.1 v = y.1 v * tf v
    by_cases h : v ∈ A.Sg ∧ v ∉ A₀.Sg
    · rw [hoff y hy v h.1]
      simp
    · simp only [tf, dif_neg h]
      simp
  have htS : t ∈ SA Δ := by
    simp only [SA, Subgroup.mem_iInf, Subgroup.mem_comap]
    intro v
    show tf v ∈ SU ((cv v) Δ)
    by_cases h : v ∈ A.Sg ∧ v ∉ A₀.Sg
    · simp only [tf, dif_pos h]
      exact (hspl v h).choose_spec.1
    · simp only [tf, dif_neg h]
      exact one_mem _
  have hj : t⁻¹ * u ∈ A.dat.U2 := by
    refine (hU2 _).2 ⟨fun v hv => ?_, fun v hv => ?_⟩
    · show eD (A.hs v hv) ((tf v)⁻¹ * u.1 v) ∈ (A.V v).J 2
      by_cases h0 : v ∈ A₀.Sg
      · have hn : ¬ (v ∈ A.Sg ∧ v ∉ A₀.Sg) := fun h => h.2 h0
        simp only [tf, dif_neg hn, inv_one, one_mul]
        rw [eD_congr (A.hs v hv) (A₀.hs v h0) (hE.s v h0), hE.V v h0]
        exact hu₀.1 v h0
      · have hp : v ∈ A.Sg ∧ v ∉ A₀.Sg := ⟨hv, h0⟩
        simp only [tf, dif_pos hp]
        rw [hE.iw v hv h0]
        exact (hspl v hp).choose_spec.2
    · show (tf v)⁻¹ * u.1 v ∈ KD ((cv v) Δ) (Ov v)
      have hn : ¬ (v ∈ A.Sg ∧ v ∉ A₀.Sg) := fun h => hv h.1
      simp only [tf, dif_neg hn, inv_one, one_mul]
      exact hu₀.2 v (fun h0 => hv (hE.sub h0))
  refine ⟨y, hy, ⟨s * t, mul_mem hs htS⟩, ?_⟩
  intro h0
  apply hg
  have hsy : s * y * u = s * t * y * (t⁻¹ * u) := by
    calc s * y * u = s * (y * t) * (t⁻¹ * u) := by group
      _ = s * (t * y) * (t⁻¹ * u) := by rw [← hcomm]
      _ = s * t * y * (t⁻¹ * u) := by group
  rw [show C.ι γ * s * y * u = C.ι γ * (s * y * u) by group, hφ.1 γ (s * y * u), hsy, hinv _ hj]
  rw [show φ (s * t * y) = 0 from h0, map_zero]

end
end

