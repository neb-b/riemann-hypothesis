module

public import Mathlib
public import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.ThetaOfCsdR
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.AscSeedHolds2
public import Development.WeilBound.RepresentationTheoryGL.ResidualSpectrum.SliceTensors.Bundle0018
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0716
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SatakeParameterSphericalProductSpehQuotients
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0002
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0653
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BaseChangeDefiniteUnitary
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0248
public import Development.WeilBound.CoreStatements.AutomorphicKernels.IsobaricBaseChange.IntegralCoefficientBaseChange.ResidualRigidity.AllPlaceRigidityResidual
public import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.Bundle0353
public import Development.WeilBound.CoreStatements.PublishedTheorems.FiniteGLInvariants.AffineLieInvariants.Imports

@[expose] public section

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LStrSat
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Rig

theorem spehExp_injective (d : ℕ) : Function.Injective (spehExp d) := fun i j h => by
  have h' : ((i : ℕ) : ℝ) = ((j : ℕ) : ℝ) := by
    unfold spehExp at h
    linarith
  exact Fin.ext (by exact_mod_cast h')

theorem strSat : StrSat := by
  intro E _ _ _ N a d V P σ hN hV hPu hPn hA hloc ν hν
  have hd : 1 ≤ d := by
    obtain ⟨hsum, -⟩ := hA
    rcases Nat.eq_zero_or_pos d with rfl | h
    · simp at hsum
      omega
    · exact h
  have hex : ∀ s : ℝ, ∃ χ : Formalism.L2.Host.HChar E, χ.IsAbsPow s :=
    fun s => ⟨_, GlobalTheory.HeckeGal.Model.absPow_isAbsPow E s⟩
  choose χ0 hχ0 using hex
  classical
  let μ : ℝ → Formalism.L2.Host.HChar E := fun s =>
    if h : ∃ k, spehExp d k = s then ν h.choose else χ0 s
  have hμ : ∀ s, (μ s).IsAbsPow s := fun s => by
    by_cases h : ∃ k, spehExp d k = s
    · simp only [μ, dif_pos h]
      have := hν h.choose
      rwa [h.choose_spec] at this
    · simp only [μ, dif_neg h]
      exact hχ0 s
  have hμk : ∀ k, μ (spehExp d k) = ν k := fun k => by
    have h : ∃ k', spehExp d k' = spehExp d k := ⟨k, rfl⟩
    simp only [μ, dif_pos h]
    rw [spehExp_injective d h.choose_spec]
  filter_upwards [GlobalTheory.SpehPair.eventually_spherical hV] with w hw
  have hsph := hw (σ w) (hloc w)
  obtain ⟨T, hT⟩ := GlobalTheory.SatInd.exists_hasSatGL_of_isIrreducible (σ w).smooth (σ w).irred hsph
  obtain ⟨τ, hτ, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp PositivityTheory.Rg.HF.GL.automorphicFormsFiniteGL E a P w
  have hS := PositivityTheory.Rg.Rs.ascSeed_holds2.2 E N a d V P hN hV hPu hPn hA w τ (σ w) hτ (hloc w)
  obtain ⟨B, hB, hBT⟩ := GlobalTheory.SpehPair.exists_sat_twist hd hτ hS hT μ hμ
  have hsum : ∑ k : Fin d, B k.rev = T := by
    rw [← hBT]
    exact Fintype.sum_equiv Fin.revPerm _ _ fun _ => rfl
  refine ⟨fun k => B k.rev, fun k => ?_, hsph, hsum ▸ hT⟩
  have := hB k.rev
  rwa [PositivityTheory.Rg.Rs.satakeAscent.spehExp_rev, neg_neg, hμk, CG.twist_mk] at this

end PositivityTheory.Rg.BcB.F.Rig

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.LWeightEx
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.F

namespace PositivityTheory.Rg.BcB.F.Rig

theorem weight_zero {E : Type} [Field E] [NumberField E] [IsCMField E] (π : Submodule ℂ (UA E 0 → ℂ))
    (hπ : IsAutRepU π) (τ : E →+* ℂ) : ∃ lam : DomWeight 0, HasWeightAt π τ lam := by
  let lam : DomWeight 0 := ⟨fun i => i.elim0, fun i => i.elim0⟩
  refine ⟨lam, GlobalTheory.DefU.isIrreducible_sqRep 0 lam, ?_⟩
  obtain ⟨φ, hφ, hφ0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hπ.ne_bot
  obtain ⟨v, hv⟩ := exists_ne (0 : nablaSq ℂ 0 lam)
  obtain ⟨c, hc⟩ : ∃ c : Module.Dual ℂ (nablaSq ℂ 0 lam), c v ≠ 0 := by
    by_contra h
    push_neg at h
    exact hv ((Module.forall_dual_apply_eq_zero_iff ℂ v).1 h)
  have hg : ∀ g : GL (Fin 0) ℂ, g = 1 := fun g => Units.ext (funext fun i => i.elim0)
  have hu : ∀ y : UA E 0, y = 1 := fun y => Subtype.ext (Units.ext (funext fun i => i.elim0))
  refine ⟨LinearMap.smulRight c φ, fun h => ?_, fun w => π.smul_mem _ hφ, fun x w => ?_⟩
  · have h1 := LinearMap.congr_fun h v
    rw [LinearMap.smulRight_apply, LinearMap.zero_apply, smul_eq_zero] at h1
    exact h1.elim hc hφ0
  · rw [hg (((cEmb τ).comp (embU 0 τ).subtype) x), hu (x : UA E 0), map_one, map_one]
    rfl

theorem weightEx : WeightEx := by
  intro E _ _ _ n π hπ τ
  rcases Nat.eq_zero_or_pos n with rfl | hn
  · exact weight_zero π hπ τ
  · exact _root_.GlobalTheory.DefU.exists_hasWeightAt_of_isAutRepU E n hn π hπ τ

theorem infOfWeight_reg {n : ℕ} (lam : DomWeight n) : (infOfWeight lam).Nodup ∧
    ∀ x ∈ infOfWeight lam, ∃ k : ℤ, x = k + ((n : ℂ) - 1) / 2 := by
  refine ⟨Multiset.Nodup.map (fun k k' h => ?_) Finset.univ.nodup, fun x hx => ?_⟩
  · have h2 : ((lam.w k - ((k : ℕ) : ℤ) : ℤ) : ℂ) = ((lam.w k' - ((k' : ℕ) : ℤ) : ℤ) : ℂ) := by
      push_cast
      linear_combination h
    have h3 : lam.w k - ((k : ℕ) : ℤ) = lam.w k' - ((k' : ℕ) : ℤ) := by exact_mod_cast h2
    rcases le_total k k' with hk | hk
    · have h4 := lam.anti hk
      have h5 : (k : ℕ) ≤ k' := hk
      exact Fin.ext (by omega)
    · have h4 := lam.anti hk
      have h5 : (k' : ℕ) ≤ k := hk
      exact Fin.ext (by omega)
  · obtain ⟨k, -, rfl⟩ := Multiset.mem_map.1 hx
    exact ⟨lam.w k - ((k : ℕ) : ℤ), by push_cast; ring⟩

theorem regPart : RegPart := by
  intro E _ _ _ n D hr i τ
  obtain ⟨lam, hlam⟩ := hr τ
  have hle : D.m i τ ≤ infOfWeight lam := by
    rw [← hlam, ← Finset.add_sum_erase Finset.univ (fun j => D.m j τ) (Finset.mem_univ i)]
    exact Multiset.le_add_right _ _
  obtain ⟨h1, h2⟩ := infOfWeight_reg lam
  exact ⟨D.m i τ, D.inf i τ, Multiset.nodup_of_le hle h1, fun x hx => h2 x (Multiset.subset_of_le hle hx)⟩

theorem rStrings : RStrings := by
  intro hR E _ _ _ n D hr i
  let τ : E →+* ℂ := (IsAlgClosed.lift : E →ₐ[ℚ] ℂ).toRingHom
  obtain ⟨m, hm, hnd, hx⟩ := hR E n D hr i τ
  have hRI : RegInt (D.V i) τ := ⟨m, hm, hnd, fun x hx' y hy => by
    obtain ⟨k, rfl⟩ := hx x hx'
    obtain ⟨k', rfl⟩ := hx y hy
    exact ⟨k - k', by push_cast; ring⟩⟩
  obtain ⟨a, d, P, hu, hn, he⟩ := ascSeed_holds2.1 E (D.N i) (D.pos i) (D.V i) (D.discrete i) τ hRI
  obtain ⟨h, -⟩ := he P (Setoid.refl (α := CuspSub E a) P)
  have hda : d * a = D.N i := by simpa using h
  have hpos := D.pos i
  refine ⟨a, d, P, ?_, ?_, hu, hn, he⟩
  · rcases Nat.eq_zero_or_pos a with ha | ha
    · rw [ha, Nat.mul_zero] at hda
      omega
    · exact ha
  · rcases Nat.eq_zero_or_pos d with hd | hd
    · rw [hd, Nat.zero_mul] at hda
      omega
    · exact hd

end PositivityTheory.Rg.BcB.F.Rig

end
end

-- bundled from Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.SatakeExponents.SatakeRigidity.OfEqOfIsSpeh
section
noncomputable section

open NumberField IsDedekindDomain Matrix
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC GlobalTheory.DiscSpec PositivityTheory.Rg.Rs

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Rg.BcB.F.Rig

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

theorem of_eq_of_isSpeh {w : HeightOneSpectrum (𝓞 E)} {N N' : ℕ} (σ : SmIrr (GL (Fin N) (w.adicCompletion E)))
    (σ' : SmIrr (GL (Fin N') (w.adicCompletion E))) (x : GlobalTheory.LocGL.IrrGL (k := w.adicCompletion E)) (d : ℕ)
    (h : GlobalTheory.LocGL.IsSpeh x d σ.ρ) (h' : GlobalTheory.LocGL.IsSpeh x d σ'.ρ) :
    GlobalTheory.LocGL.IrrGL.of σ.ρ σ.smooth σ.irred = GlobalTheory.LocGL.IrrGL.of σ'.ρ σ'.smooth σ'.irred := by
  obtain ⟨hd, hc⟩ := h
  obtain ⟨hd', hc'⟩ := h'
  obtain rfl : N = N' := hd.symm.trans hd'
  exact GlobalTheory.LocGL.IrrGL.of_eq_of.2 (GlobalTheory.LocGL.IsCosocle.unique hc' hc)

theorem ascEmb_of_sigma {N a a' d : ℕ} {V : Submodule ℂ (Sm E N)} (P : CuspSub E a) (P' : CuspSub E a')
    (h : ∀ P'' : CuspSub E a', P'.Iso P'' → AscEmb V P'' d)
    (e : (⟨a', CG.mk P'⟩ : Σ b, CG E b) = ⟨a, CG.mk P⟩) : AscEmb V P d := by
  obtain ⟨rfl, he⟩ := Sigma.mk.inj_iff.mp e
  exact h P (Quotient.exact (eq_of_heq he))

theorem rLoc : RLoc := by
  intro hJS hSS hStr E _ _ _ n D D' hr hr' hsat
  choose a d P ha hd hPu hPn hPs using hStr E n D hr
  choose a' d' P' ha' hd' hPu' hPn' hPs' using hStr E n D' hr'
  have he : ∀ i, AscEmb (D.V i) (P i) (d i) := fun i => hPs i (P i) (Setoid.refl (α := CuspSub E (a i)) (P i))
  have he' : ∀ j, AscEmb (D'.V j) (P' j) (d' j) := fun j =>
    hPs' j (P' j) (Setoid.refl (α := CuspSub E (a' j)) (P' j))
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow E
  have h1 := Filter.eventually_all.2 fun i => hSS E (D.N i) (a i) (d i) (D.V i) (P i) (D.σ i) (D.pos i)
    (D.discrete i) (hPu i) (hPn i) (he i) (D.loc i) (fun k => GlobalTheory.HeckeGal.Model.absPow E (spehExp (d i) k))
    (fun k => hν _)
  have h2 := Filter.eventually_all.2 fun j => hSS E (D'.N j) (a' j) (d' j) (D'.V j) (P' j) (D'.σ j) (D'.pos j)
    (D'.discrete j) (hPu' j) (hPn' j) (he' j) (D'.loc j) (fun k => GlobalTheory.HeckeGal.Model.absPow E (spehExp (d' j) k))
    (fun k => hν _)
  obtain ⟨s, hs⟩ := GlobalTheory.Published.JacquetShalikaRigidity.unitary hJS (ι := Σ i, Fin (d i)) (κ := Σ j, Fin (d' j))
    (fun x => CG.mk (P x.1)) (fun y => CG.mk (P' y.1)) (fun x => ha x.1) (fun y => ha' y.1)
    (fun x => (CG.isUnitary_mk _).2 (hPu x.1)) (fun y => (CG.isUnitary_mk _).2 (hPu' y.1)) _ hν
    (fun x => spehExp (d x.1) x.2) (fun y => spehExp (d' y.1) y.2) (by
      filter_upwards [h1, h2, hsat] with w hw hw' hB
      obtain ⟨B, ⟨b, hb, hbB⟩, ⟨b', hb', hbB'⟩⟩ := hB
      choose c hc hsph hcs using hw
      choose c' hc' hsph' hcs' using hw'
      refine ⟨fun x => c x.1 x.2, fun y => c' y.1 y.2, fun x => hc x.1 x.2, fun y => hc' y.1 y.2, ?_⟩
      rw [Fintype.sum_sigma, Fintype.sum_sigma]
      have e1 : ∀ i, ∑ k, c i k = b i := fun i => (hcs i).unique (hb i).2
      have e2 : ∀ j, ∑ k, c' j k = b' j := fun j => (hcs' j).unique (hb' j).2
      simp only [e1, e2]
      exact hbB.trans hbB'.symm)
  have hstr := GlobalTheory.Rigid.strings_eq_of_equiv (fun i => (⟨a i, CG.mk (P i)⟩ : Σ b, CG E b)) d
    (fun j => (⟨a' j, CG.mk (P' j)⟩ : Σ b, CG E b)) d' s fun x => ⟨(hs x).1, (hs x).2⟩
  obtain ⟨s0, hs0⟩ := GlobalTheory.T.multiset_of_strings_determines_points_degrees _ d _ d' hd hd' hstr
  refine ⟨s0, fun i w => ?_⟩
  have hA : AscEmb (D'.V (s0 i)) (P i) (d i) := by
    rw [(hs0 i).2]
    exact ascEmb_of_sigma (P i) (P' (s0 i)) (hPs' (s0 i)) (hs0 i).1.symm
  obtain ⟨σ0, hσ0, -⟩ := GlobalTheory.CuspRep.LocEx.exists_isLocComp CuspFormAutomorphicBounds.automorphicFormsFiniteGL E (a i) (P i) w
  have k1 := ascSeed_holds2.2 E (D.N i) (a i) (d i) (D.V i) (P i) (D.pos i) (D.discrete i) (hPu i) (hPn i) (he i)
    w σ0 (D.σ i w) hσ0 (D.loc i w)
  have k2 := ascSeed_holds2.2 E (D'.N (s0 i)) (a i) (d i) (D'.V (s0 i)) (P i) (D'.pos _) (D'.discrete _) (hPu i)
    (hPn i) hA w σ0 (D'.σ (s0 i) w) hσ0 (D'.loc _ w)
  exact of_eq_of_isSpeh _ _ _ _ k1 k2

end PositivityTheory.Rg.BcB.F.Rig

end
end

