module

public import Mathlib
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0050
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0052
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0054
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.Bundle0060
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.HermitianPartLeLevi
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.LeviNormalizesUnipotentVariant
public import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ArchimedeanIwasawaMinimalParabolic
public import Development.WeilBound.RepresentationTheoryGL.ConstantTermFiniteness.CuspidalConstantTerms.CoeffSpanCompMem
public import GroundTheory.PAdicHodge.NormalizedTrace

@[expose] public section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.Published GlobalTheory.Published.AutFin GlobalTheory.StdPar GlobalTheory.ThK.SmoothLev GlobalTheory.CompanionTheory.Hypotheses₂.ConstFin GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart
open GlobalTheory.UAut GlobalTheory.AdelicU GlobalTheory.SiegelSet

noncomputable section

namespace GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Rg

theorem finite_slices_uPart : ∀ (D : D7) (θ : D.what₂.Tau → (Ainf D.host.F ⊗[D.host.F] D.host.E →+* ℂ)), IsInfFam θ → ∀ (V : HSp D) (U : Subgroup (GA D V)), IsOpen (U : Set (GA D V)) → ∀ (ε : D.what₂.Tau → Fin V.rank → Bool) (fr : D.what₂.Tau → Matrix (Fin V.rank) (Fin V.rank) ℂ), IsFrameFam V ε fr → ∀ (W : D.what₂.Tau → Type) [∀ τ, AddCommGroup (W τ)] [∀ τ, Module ℂ (W τ)] [∀ τ, FiniteDimensional ℂ (W τ)] (ρ : ∀ τ, Representation ℂ (Formalism.REAL.KG (ε τ)) (W τ)), (∀ τ, IsContRep (ρ τ)) → ∀ (c : D.what₂.Tau → ℕ → ℂ) (m : ℕ) (X Y : Matrix (Fin V.rank) (Fin m) D.host.E), GlobalTheory.SiegelSet.IsWittFrame D.sp.cm.sig V.gram X Y → ∀ T : Finset (Fin m), T.Nonempty → ∀ b : GA D V, FiniteDimensional ℂ (Submodule.span ℂ (sliceSet (cuspOn θ V X Y T U ε fr ρ c) (uPart D.sp.cm.sig V.gram X Y T) (levi D.sp.cm.sig V.gram X Y T) b)) := by
  intro D θ hθ V U hU ε fr hfr W _ _ _ ρ hρ c m X Y hWF T hT b
  obtain ⟨n, hn, mm, hmm, b₀, hb, had⟩ := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.iwasawa_adapted D θ hθ V ε fr hfr m X Y hWF T b
  obtain ⟨mH, hmH, mo, hmo, hcomm, rfl⟩ := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.USplit.exists_split D V m X Y hWF T mm hmm
  subst hb
  have hU' : IsOpen ((U.map (MulAut.conj b₀).toMonoidHom : Subgroup (GA D V)) : Set (GA D V)) := by
    have e : ((U.map (MulAut.conj b₀).toMonoidHom : Subgroup (GA D V)) : Set (GA D V)) =
        (fun x => b₀⁻¹ * x * b₀) ⁻¹' (U : Set (GA D V)) := by
      ext x
      simp only [Subgroup.coe_map, Set.mem_image, SetLike.mem_coe, Set.mem_preimage, MulEquiv.coe_toMonoidHom,
        MulAut.conj_apply]
      constructor
      · rintro ⟨u, hu, rfl⟩
        simpa [mul_assoc] using hu
      · intro hx
        exact ⟨b₀⁻¹ * x * b₀, hx, by group⟩
    rw [e]
    exact hU.preimage (by fun_prop)
  have hfr' := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.isFrameFam_mul_infMat_inv D θ hθ V ε fr hfr b₀
  have hfin := finite_slices_core D θ hθ V _ hU' ε _ hfr' W ρ hρ c m X Y hWF T hT had
  set H := uPart D.sp.cm.sig V.gram X Y T with hH
  set L := levi D.sp.cm.sig V.gram X Y T with hL
  let mH' : H := ⟨mH, hmH⟩
  let R : (H → ℂ) →ₗ[ℂ] (H → ℂ) :=
    { toFun := fun f t => f (t * mH')
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hsub : sliceSet (cuspOn θ V X Y T U ε fr ρ c) H L (n * (mH * mo) * b₀) ⊆
      ((Submodule.span ℂ (sliceSet (cuspOn θ V X Y T (U.map (MulAut.conj b₀).toMonoidHom) ε
        (fun τ => fr τ * (infMat D.sp.cm.sig V.gram (θ τ) b₀)⁻¹) ρ c) H L 1)).map R : Set (H → ℂ)) := by
    rintro f ⟨φ, hφ, y, hy, hyc, rfl⟩
    refine ⟨fun t : H => φ ((t : GA D V) * (y * mo) * b₀),
      Submodule.subset_span ⟨fun x => φ (x * b₀), _root_.GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Transl.cuspOn_mul_right D θ hθ V U ε fr hfr W ρ c m X Y T φ hφ b₀, y * mo,
        mul_mem hy hmo, fun t ht => ?_, ?_⟩, ?_⟩
    · rw [← mul_assoc, hyc t ht, mul_assoc, hcomm t ht, mul_assoc]
    · funext t
      simp [mul_assoc]
    · funext t
      have ht : (t : GA D V) ∈ L := _root_.GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.uPart_le_levi D V m X Y T t.2
      have hty : (t : GA D V) * y ∈ L := mul_mem ht hy
      have hγ : (t : GA D V) * y * n * ((t : GA D V) * y)⁻¹ ∈ unip D.sp.cm.sig V.gram X T :=
        _root_.GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.conj_mem_unip_of_mem_levi D V m X Y hWF T _ hty n hn
      have hleft := hφ.1.1.left _ (Subgroup.mem_sup_left hγ : _ ∈ (leftSub V X Y T : Subgroup (GA D V)))
        ((t : GA D V) * y * (mH * mo * b₀))
      have e1 : (t : GA D V) * y * n * ((t : GA D V) * y)⁻¹ * ((t : GA D V) * y * (mH * mo * b₀)) =
          (t : GA D V) * y * (n * (mH * mo) * b₀) := by group
      have e2 : (t : GA D V) * y * (mH * mo * b₀) = (t : GA D V) * mH * (y * mo) * b₀ := by
        have := hyc mH hmH
        calc (t : GA D V) * y * (mH * mo * b₀) = (t : GA D V) * (y * mH) * mo * b₀ := by group
          _ = (t : GA D V) * (mH * y) * mo * b₀ := by rw [this]
          _ = (t : GA D V) * mH * (y * mo) * b₀ := by group
      change φ ((t : GA D V) * mH * (y * mo) * b₀) = φ ((t : GA D V) * y * (n * (mH * mo) * b₀))
      rw [← e1, hleft, e2]
  haveI := hfin
  exact Submodule.finiteDimensional_of_le (Submodule.span_le.2 hsub)

end GlobalTheory.CompanionTheory.Hypotheses₂.LeviPart.UCore.Rg

end
