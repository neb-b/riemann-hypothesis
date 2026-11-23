module

public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.ExistsLin
public import Development.AutomorphicArithmetic.CommutativeAlgebra.EtaleCohomology.CardResOK
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.CrystallineTowers.LocTowerHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.RepMain
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PCutStep
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.Bundle0002
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.CharPolEqRootPol
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.BasicOpenSections.EsStepHolds
public import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.SplitLineSubtraction.Bundle0005

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PGeoSide
section
theorem UpperTheory.Gal.Int.Geo.geoSide_of :
    UpperTheory.Gal.crystallineComparison.Br.FinAll → CrystallineSemistableComparison.SmoothModelCrystalline → UpperTheory.Ru.crystallineComparison.GeoSide := by
  intro hFin hCr E Ω _ _ _ _ _ l _ H θ hN a ρ₀ hMat w hw n ϑ hCong P AI hT A hA O _ _ _ Bw hj
  obtain ⟨hD, hDV, hf, hnorm, hcard, C, hOnto, hCg⟩ :=
    UpperTheory.Ru.crystallineComparison.congBC E Ω l _ H θ w hw n ϑ hCong A hA O Bw hj
  obtain ⟨ρ₁, hM₁, hρ₁⟩ :=
    UpperTheory.Gal.Seam.locTower_holds l E ↥Bw.Kw.1 Ω _
      (UpperTheory.Gal.Seam.kOf Bw) Bw.j (fun _ => rfl) H hN _ θ a ρ₀ hMat
  obtain ⟨V, i₁, i₂, i₃, ρ, T, b, hcr, hann, hinj, hact, heig⟩ :=
    UpperTheory.Ru.crystallineComparison.geoLoc hFin hCr l P AI hT Bw.Kw _ hf hcard
      (UpperTheory.Gal.Int.Geo.bcAlong H (UpperTheory.Gal.Seam.kOf Bw)) θ
      (UpperTheory.Gal.Seam.niceBc _ _ (UpperTheory.Gal.Seam.kOf Bw) H hN) C hOnto n ϑ hCg a ρ₁ hM₁
  rw [hnorm]
  refine ⟨V, i₁, i₂, i₃, ρ, T, b, hcr, hann, hinj, fun g x => ?_, heig⟩
  have h := hact (Bw.e g) x
  rwa [hρ₁ (g : Ω ≃ₐ[E] Ω) _ fun y => Bw.e_comm g y] at h
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.StepsMain
section
namespace UpperTheory.Gal.Int.Geo

theorem steps_of (hC : CrysStep) (hJ : JumpStep) (hP : PhiStep) : Steps :=
  ⟨repEx_holds, Mod.esStep_holds, hC, hJ, hP, cutStep_holds, twES, twCrys, twJ, twPhi, phiOf, satCard, jumpsOf, richOf,
    TP.Sub.charEx, TP.Sub.sSLeft_holds, TP.Sub.contLeft_holds⟩

end UpperTheory.Gal.Int.Geo
end

