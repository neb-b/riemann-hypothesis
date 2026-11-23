module

public import Mathlib
public import Development.AbelianVarietyTheory.Statements.EllipticCurveLevels.HasLevel
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.MatchOfMatchOffTEmpty
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.RegPolOfRepOf
public import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.Imports
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.ArthurClozelStrongTC
public import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0009
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0281
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0203
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0198
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsLocCompAndIsLocLoc
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0112
public import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1678
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0023
public import Formalism.LocalToGlobal.Columns.Bundle0035
public import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
public import Formalism.LocalToGlobal.GlobalTheory.GL6.PBwLocBases
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0282
public import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FirstCoupledKernelEquivariantCosets
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0277
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0262
public import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0280

@[expose] public section

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ApartOfNotMem
section
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.GalCut GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.Published GlobalTheory.AboveL

namespace GlobalTheory.Cong.OffTLimit

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {l : ℕ} [Fact l.Prime] {a : ℕ}

theorem apart_of_not_mem {w₀ w : HeightOneSpectrum (𝓞 E)} (h₀ : ((l : ℕ) : 𝓞 E) ∈ w₀.asIdeal)
    (hw : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) : Apart w w₀ := by
  intro h
  apply hw
  have h1 : ((l : ℕ) : 𝓞 (maximalRealSubfield E)) ∈ (w₀.under (𝓞 (maximalRealSubfield E))).asIdeal := by
    rw [HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast]; exact h₀
  rw [← h, HeightOneSpectrum.under_asIdeal, Ideal.under_def, Ideal.mem_comap, map_natCast] at h1
  exact h1

theorem z_eq_of_equiv {ι : Qbar l ≃+* ℂ} {Kw : Levels E a} {J : Type} (O : LocOps l ι Kw J) (j : J)
    {σ σ' : SmIrr (GL (Fin a) ((O.pl j).adicCompletion E))} (e : σ.ρ.Equiv σ'.ρ)
    (hne : PRep.fixed σ.ρ (Kw (O.pl j)) ≠ ⊥) : O.z j σ = O.z j σ' := by
  obtain ⟨v, hv, hv0⟩ := (Submodule.ne_bot_iff _).1 hne
  have he : ∀ g u, e.toLinearEquiv (σ.ρ g u) = σ'.ρ g (e.toLinearEquiv u) := fun g u =>
    LinearMap.congr_fun (e.isIntertwining' g) u
  have hv' : e.toLinearEquiv v ∈ PRep.fixed σ'.ρ (Kw (O.pl j)) := by
    change ∀ h : Kw (O.pl j), σ'.ρ (h : GL (Fin a) ((O.pl j).adicCompletion E)) (e.toLinearEquiv v) =
      ((1 : Kw (O.pl j) →* ℂˣ) h : ℂ) • e.toLinearEquiv v
    intro h
    have := hv h
    simp only [MonoidHom.one_apply, Units.val_one, one_smul] at this ⊢
    rw [← he, this]
  have hop : e.toLinearEquiv (opOf σ.ρ (O.f j) v) = opOf σ'.ρ (O.f j) (e.toLinearEquiv v) := by
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [opOf, Finsupp.sum, map_sum, map_smul, he]
  have h2 := O.act j σ' _ hv'
  rw [← hop, O.act j σ v hv, map_smul] at h2
  have hne' : e.toLinearEquiv v ≠ 0 := by simpa using hv0
  exact smul_left_injective ℂ hne' h2

end GlobalTheory.Cong.OffTLimit

namespace GlobalTheory.Cong

end GlobalTheory.Cong
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFunctionalEqOfAgreeAtBadPlaces
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.TwV.FnlAway
open scoped TensorProduct

variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
  {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}

theorem exists_place {A : AdData t u μ St} {dtU : Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm →* D.Dt} {a : 𝓞 D.host.E} (H : AdTie A dtU a)
    (j : ℕ) (hj : j ≤ D.R.m) (P : t.Pr.vT (t.word u)) :
    ∃ v : HeightOneSpectrum (𝓞 D.host.F), ∃ h : (((St j hj).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal,
      IsOver v (seamP t.seam P.1) ∧ v ∈ plUnder D.host.F (ssRec t u μ) := by
  classical
  obtain ⟨hSS, -⟩ := t.rd_chain u μ
  have hpi : t.Pr.piT (t.word u) ∈ P.1.asIdeal := by
    have h := P.2
    unfold Formalism.L2.Col.Primes.vT Formalism.L2.Col.divs at h
    split_ifs at h with hf
    · simpa using h
    · simp at h
  have hT : ((t.Pr.T (t.word u) : ℕ) : 𝓞 t.X.E) ∈ P.1.asIdeal := by
    rw [← t.pr_ok.piT_norm]
    exact Ideal.mul_mem_right _ _ hpi
  have hTQ : (((St j hj).T : ℕ) : 𝓞 D.host.E) ∈ (seamP t.seam P.1).asIdeal := by
    rw [H.T_eq j hj, ← t.T_rec u, ← map_natCast (RingOfIntegers.mapRingEquiv t.seam.iE), mem_seamP]
    exact hT
  have hT0 : (((St j hj).T : ℕ) : 𝓞 D.host.F) ≠ 0 := by
    rw [H.T_eq j hj, ← t.T_rec u]
    exact Nat.cast_ne_zero.2 (t.pr_ok.T_prime _).ne_zero
  have hmem : (((St j hj).T : ℕ) : 𝓞 D.host.F) ∈ (seamP t.seam P.1).asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    rw [Ideal.mem_comap, map_natCast]
    exact hTQ
  let v : HeightOneSpectrum (𝓞 D.host.F) := ⟨(seamP t.seam P.1).asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)),
    Ideal.IsPrime.comap _, fun h => hT0 (by rw [h] at hmem; exact (Ideal.mem_bot.1 hmem))⟩
  refine ⟨v, hmem, rfl, seamP t.seam P.1, ?_, rfl⟩
  refine (mem_ssRec t u μ P.1).2 ?_
  rw [hSS]
  unfold Sall
  exact Finset.mem_union.2 (Or.inl P.2)

theorem prV_pullV_congr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (c : GL (Fin N) E) (x x₁ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (h : bc (prV (E := E) v) x₁ = bc (prV (E := E) v) x) (y : Fin N → E) (l : Fin N) :
    prV (E := E) v (pullV (F := F) (ratA F c * x₁) y l) = prV (E := E) v (pullV (F := F) (ratA F c * x) y l) := by
  have key : ∀ z : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F), prV (E := E) v (pullV (F := F) z y l) =
      ((((bc (prV (E := E) v) z)⁻¹ : GL (Fin N) (E ⊗[F] v.adicCompletion F)) : Matrix (Fin N) (Fin N) (E ⊗[F] v.adicCompletion F)) *ᵥ
        fun i => prV (E := E) v (iA F E (y i))) l := by
    intro z
    rw [← map_inv]
    exact RingHom.map_mulVec (prV (E := E) v) _ _ l
  rw [key, key, map_mul, map_mul, h]

theorem mem_latS_of_latCo {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E]
    (sp : Spaces R F E) {N : ℕ} (J : Matrix (Fin N) (Fin N) E) (hJ : IsUnit J.det) (c : GL (Fin N) E) (a : 𝓞 E)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hx : x ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F))
    (Lb : Submodule (𝓞 E) (Fin N → E)) (hfin : Module.Finite (𝓞 E) Lb) (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤)
    (hint : ∀ y ∈ Lb, y ∈ dualSet (sp.cm.sig : E →+* E) J Lb) (v : HeightOneSpectrum (𝓞 F)) (y : Fin N → E)
    (hy : y ∈ latCo sp J c a x Lb) :
    (fun l => prV (E := E) v (pullV (F := F) (ratA F c * x) y l)) ∈
      latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J Lb)) :=
  GlobalTheory.T.pulledLatticeVector_mem_dualBaseLatticeCompletion sp J hJ c a x hx Lb hfin hspan hint v y hy

theorem fnl_away : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
  (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
  (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
  ∀ (P : t.Pr.vT (t.word u)) (w : Sp t.X.E (D.R.N j)), w ∈ p.deco.1.at P.1 → w ∈ p₁.deco.1.at P.1 → p₁.deco.1.f P w = p.deco.1.f P w) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hPin H j hj β x x₁ p p₁ hp hp₁ hag P w hw hw₁
  obtain ⟨v, hTv, hov, hvU⟩ := exists_place H j hj P
  have hxv := hag v hvU
  obtain ⟨s, hs, hsw⟩ := (mem_locP _ _ _).1 hw
  obtain ⟨s', hs', hsw'⟩ := (mem_locP _ _ _).1 hw₁
  have h1 : (s' * s) • w ∈ p.deco.1.N := by rw [mul_smul]; exact Submodule.smul_mem _ _ hsw
  have h2 : (s' * s) • w ∈ p₁.deco.1.N := by rw [mul_comm, mul_smul]; exact Submodule.smul_mem _ _ hsw'
  have hmem : ∀ (y : UA D j hj) (q : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β y q →
      ∀ w' ∈ q.deco.1.N, (fun l => prV (E := D.host.E) v (pullV (F := D.host.F) (ratA D.host.F (A.crd j hj) * y.1)
        (fun b => t.seam.iE (w' b)) l)) ∈ latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D j hj) ((St j hj).K β).lev.Lb)) := by
    intro y q hq w' hw'
    have hy : (fun b => t.seam.iE (w' b)) ∈ latCo D.sp (gramN D j hj) (A.crd j hj) a y.1 ((St j hj).K β).lev.Lb := by
      rw [← hq.lat]
      exact Submodule.subset_span ⟨w', hw', rfl⟩
    exact mem_latS_of_latCo D.sp (gramN D j hj) (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D j hj) (A.crd j hj) a y.1 y.2
      _ ((St j hj).K β).lev.Lb_fin ((St j hj).K β).lev.Lb_span ((St j hj).K β).lev.Lb_int v _ hy
  let z : latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
      (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D j hj) ((St j hj).K β).lev.Lb)) :=
    ⟨_, hmem x p hp _ h1⟩
  have e1 := hp.fnl P v hTv hov _ h1 z rfl
  have e2 := hp₁.fnl P v hTv hov _ h2 z (by
    funext l
    exact (prV_pullV_congr v (A.crd j hj) x.1 x₁.1 hxv _ l).symm)
  have e3 : p₁.deco.1.f P ((s' * s) • w) = p.deco.1.f P ((s' * s) • w) := e2.trans e1.symm
  rw [p₁.deco.2.f_smul P _ w hw₁, p.deco.2.f_smul P _ w hw] at e3
  haveI hP := P.1.isPrime
  have hu : Ideal.Quotient.mk P.1.asIdeal (s' * s) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact fun hm => (hP.mem_or_mem hm).elim hs' hs
  exact mul_left_cancel₀ hu e3

end GlobalTheory.TwV.FnlAway

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFunctionalEqOfAgreeBadPlacesAllSteps
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV Formalism.UG
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.TwV.FnlAwayCpl

section Loc
variable {E : Type} [Field E] [NumberField E] [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

theorem f_eq_on_at {d d₁ : Deco E n ST SG} (hd : d.Ok) (hd₁ : d₁.Ok) (P : ST) (hat : d₁.at P.1 = d.at P.1)
    (h : ∀ w ∈ d.N, w ∈ d₁.N → d₁.f P w = d.f P w) : ∀ y ∈ d.at P.1, d₁.f P y = d.f P y := by
  intro y hy
  have hy₁ : y ∈ d₁.at P.1 := hat ▸ hy
  obtain ⟨s, hs, hsy⟩ := (mem_locP P.1 d.N y).1 hy
  obtain ⟨s₁, hs₁, hsy₁⟩ := (mem_locP P.1 d₁.N y).1 hy₁
  have hw : (s * s₁) • y ∈ d.N := by
    rw [mul_comm, mul_smul]; exact d.N.smul_mem s₁ hsy
  have hw₁ : (s * s₁) • y ∈ d₁.N := by
    rw [mul_smul]; exact d₁.N.smul_mem s hsy₁
  have e := h _ hw hw₁
  rw [hd₁.f_smul P _ y hy₁, hd.f_smul P _ y hy] at e
  have hne : Ideal.Quotient.mk P.1.asIdeal (s * s₁) ≠ 0 := by
    rw [Ne, Ideal.Quotient.eq_zero_iff_mem]
    exact fun hm => (P.1.isPrime.mem_or_mem hm).elim hs hs₁
  letI := Ideal.Quotient.field P.1.asIdeal
  exact mul_left_cancel₀ hne e
end Loc

section Pull
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

theorem prV_pullV_congr (v : HeightOneSpectrum (𝓞 F)) {g g₁ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)}
    (h : bc (prV (E := E) v) g₁ = bc (prV (E := E) v) g) (u : Fin N → E) :
    (fun l => prV (E := E) v (pullV (F := F) g₁ u l)) = fun l => prV (E := E) v (pullV (F := F) g u l) := by
  have h' : bc (prV (E := E) v) g₁⁻¹ = bc (prV (E := E) v) g⁻¹ := by rw [map_inv, map_inv, h]
  funext l
  unfold pullV
  rw [RingHom.map_mulVec, RingHom.map_mulVec]
  have h2 : ((g₁⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) _).map (prV (E := E) v) =
      ((g⁻¹ : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) : Matrix (Fin N) (Fin N) _).map (prV (E := E) v) := congrArg Units.val h'
  rw [h2]
end Pull
end GlobalTheory.TwV.FnlAwayCpl

namespace GlobalTheory.TwV.FnlAwayCpl
section Z
variable {R : Ranks} {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [StarRing E] [Algebra F E] {N : ℕ}

theorem exists_latS_pullV (sp : Spaces R F E) (J : Matrix (Fin N) (Fin N) E) (crd : GL (Fin N) E) (a : 𝓞 E)
    (x : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (hx : x ∈ UPts sp.cm.sig J (FiniteAdeleRing (𝓞 F) F)) (hJ : IsUnit J.det)
    (Lb : Submodule (𝓞 E) (Fin N → E)) (hfin : Module.Finite (𝓞 E) Lb)
    (hspan : Submodule.span E (Lb : Set (Fin N → E)) = ⊤)
    (hint : ∀ y ∈ Lb, y ∈ dualSet (sp.cm.sig : E →+* E) J Lb)
    (v : HeightOneSpectrum (𝓞 F)) (u : Fin N → E) (hu : u ∈ latCo sp J crd a x Lb) :
    ∃ z : latS (F := F) (v.adicCompletion F) (intV E v) (Submodule.span (𝓞 E) (dualSet (sp.cm.sig : E →+* E) J Lb)),
      z.1 = fun l => prV (E := E) v (pullV (F := F) (ratA F crd * x) u l) :=
  GlobalTheory.T.companionLatticeVector_local_mem_dualBaseCompletion sp J crd a x hx hJ Lb hfin hspan hint v u hu
end Z
end GlobalTheory.TwV.FnlAwayCpl

namespace GlobalTheory.TwV.FnlAwayCpl

theorem exists_place {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    {A : AdData t u μ St} {dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt} {a : 𝓞 D.host.E}
    (hTie : AdTie A dtU a) (P : t.Pr.vT (t.word u)) :
    ∃ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) ∧
      (∀ j (hj : j ≤ D.R.m), (((St j hj).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal) ∧ v ∈ plUnder D.host.F (ssRec t u μ) := by
  classical
  have hpi : t.Pr.piT (t.word u) ∈ P.1.asIdeal := by
    have h := P.2
    unfold Primes.vT divs at h
    split_ifs at h with hf
    · simpa using h
    · simp at h
  have hT : (((D.mem u).A.T : ℕ) : 𝓞 t.X.E) ∈ P.1.asIdeal := by
    rw [← t.T_rec u, ← t.pr_ok.piT_norm]
    exact Ideal.mul_mem_right _ _ hpi
  have hTQ : (((D.mem u).A.T : ℕ) : 𝓞 D.host.E) ∈ (seamP t.seam P.1).asIdeal := by
    have := (mem_seamP t.seam P.1 _).2 hT
    rwa [map_natCast] at this
  have hT0 : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ≠ 0 := by
    rw [← t.T_rec u]
    exact_mod_cast (t.pr_ok.T_prime (t.word u)).ne_zero
  have hTv : (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ (seamP t.seam P.1).asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)) := by
    rw [Ideal.mem_comap, map_natCast]; exact hTQ
  refine ⟨⟨(seamP t.seam P.1).asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E)), Ideal.comap_isPrime _ _,
    fun h0 => hT0 (by rw [h0] at hTv; exact (Submodule.mem_bot _).1 hTv)⟩, rfl, fun j hj => ?_, ?_⟩
  · rw [hTie.T_eq j hj]; exact hTv
  · have hSS : P.1 ∈ (t.rd u μ).SS := by
      rw [((isChainTop_iff _ _ _ _ _ _ _ _ _).1 hTie.isChainTop).1]
      exact Finset.mem_union_left _ P.2
    exact ⟨_, (mem_ssRec t u μ P.1).2 hSS, rfl⟩

end GlobalTheory.TwV.FnlAwayCpl

namespace GlobalTheory.TwV

open Formalism.L2.Forms


set_option maxHeartbeats 2000000 in
open FnlAwayCpl in
theorem fnl_eq_of_away_cpl : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ j (hj : j ≤ D.R.m) β x x₁ p p₁,
    IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    (∀ v ∈ plUnder D.host.F (ssRec t u μ), bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ P : t.Pr.vT (t.word u), p₁.deco.1.at P.1 = p.deco.1.at P.1 → ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y) := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a _hPins hTie j hj β x x₁ p p₁ hp hp₁ hag P hat
  obtain ⟨v, hov, hTv, hvU⟩ := exists_place hTie P
  have hfnl := hp.fnl P v (hTv j hj) hov
  have hfnl₁ := hp₁.fnl P v (hTv j hj) hov
  refine f_eq_on_at p.deco.2 p₁.deco.2 P hat fun w hw hw₁ => ?_
  have hu : (fun l => t.seam.iE (w l)) ∈ latCo D.sp (gramN D j hj) (A.crd j hj) a x.1 ((St j hj).K β).lev.Lb := by
    rw [← hp.lat]
    exact Submodule.subset_span ⟨w, hw, rfl⟩
  obtain ⟨z, hz⟩ := exists_latS_pullV D.sp (gramN D j hj) (A.crd j hj) a x.1 x.2 (Formalism.L2.GlobalTheoryTheory.LocalLatticeBases.bwB_gramN_det D j hj) ((St j hj).K β).lev.Lb
    ((St j hj).K β).lev.Lb_fin ((St j hj).K β).lev.Lb_span ((St j hj).K β).lev.Lb_int v _ hu
  have hg : bc (prV (E := D.host.E) v) (ratA D.host.F (A.crd j hj) * x₁.1) = bc (prV (E := D.host.E) v) (ratA D.host.F (A.crd j hj) * x.1) := by
    rw [map_mul, map_mul, hag v hvU]
  rw [hfnl₁ w hw₁ z (hz.trans (prV_pullV_congr v hg _).symm), hfnl w hw z hz]

end GlobalTheory.TwV
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartFunctionalEqOfAgreeUnderLevelPrime
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open Formalism.UG (bc prV)

namespace GlobalTheory.FnlAway

open Matrix Formalism.UG Formalism.L2.PairingIndexBounds.F Formalism.L2.Forms Formalism.MainNotions.G.KAat
open scoped TensorProduct

attribute [local instance] Formalism.BasicNotions.Host.cmStar

theorem T_mem_under {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} (t : KerEntTied ex) (u : D.what₂.Word) (P : t.Pr.vT (t.word u))
    (v : HeightOneSpectrum (𝓞 D.host.F)) (hv : IsOver v (seamP t.seam P.1)) :
    (((D.mem u).A.T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
  have h1 : ((t.Pr.T (t.word u) : ℕ) : 𝓞 t.X.E) ∈ P.1.asIdeal := by
    have := Ideal.absNorm_mem P.1.asIdeal
    rwa [t.pr_ok.vT_norm _ P.1 P.2] at this
  rw [t.T_rec] at h1
  have h2 := (mem_seamP t.seam P.1 _).2 h1
  rw [map_natCast] at h2
  unfold IsOver at hv
  rw [hv, Ideal.mem_comap, map_natCast]
  exact h2

theorem prV_pullV_congr {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}
    (v : HeightOneSpectrum (𝓞 F)) (g g₁ : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F))
    (h : bc (prV (E := E) v) g₁ = bc (prV (E := E) v) g) (w : Fin n → E) (l : Fin n) :
    prV (E := E) v (pullV (F := F) g₁ w l) = prV (E := E) v (pullV (F := F) g w l) := by
  have key : ∀ k : GL (Fin n) (E ⊗[F] FiniteAdeleRing (𝓞 F) F), prV (E := E) v (pullV (F := F) k w l) =
      ∑ j, ((bc (prV (E := E) v) k)⁻¹ : GL (Fin n) _).1 l j * prV (E := E) v (Formalism.L2.Col.iA F E (w j)) := by
    intro k
    rw [← map_inv]
    unfold pullV
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [Matrix.mulVec, dotProduct, map_sum, map_mul]
    rfl
  rw [key, key, h]


set_option maxHeartbeats 6000000 in
set_option synthInstance.maxHeartbeats 200000 in
theorem exists_unit_one_add_generator {D : D7} (i : ℕ) (hi : i ≤ D.R.m) {T f : ℕ} {bad : Set (HeightOneSpectrum (𝓞 D.host.F))}
    (lev : StepLevel D.host.F D.host.E (sigD D) (gramN D i hi) T f bad)
    (crd : GL (Fin (D.R.N i)) D.host.E) (a : 𝓞 D.host.E) (x : UA D i hi) (v : HeightOneSpectrum (𝓞 D.host.F))
    (w : Fin (D.R.N i) → D.host.E) (hw : w ∈ latCo D.sp (gramN D i hi) crd a x.1 lev.Lb) :
    ∃ z : latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
        (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb)),
      z.1 = fun l => prV (E := D.host.E) v (pullV (F := D.host.F) (ratA D.host.F crd * x.1) w l) := by
  let M := latS (F := D.host.F) (v.adicCompletion D.host.F) (intV D.host.E v)
    (Submodule.span (𝓞 D.host.E) (dualSet (sigD D : D.host.E →+* D.host.E) (gramN D i hi) lev.Lb))
  have hint : ∀ c : 𝓞 D.host.E, inclE (F := D.host.F) (v.adicCompletion D.host.F) (c : D.host.E) ∈ intV D.host.E v :=
    fun c => Subring.subset_closure (Or.inl ⟨⟨(c : D.host.E), ⟨c, rfl⟩⟩, rfl⟩)
  let φ : (Fin (D.R.N i) → D.host.E) → (Fin (D.R.N i) → D.host.E ⊗[D.host.F] v.adicCompletion D.host.F) :=
    fun l k => prV (E := D.host.E) v (pullV (F := D.host.F) x.1 l k)
  have hadd : ∀ l₁ l₂, φ (l₁ + l₂) = φ l₁ + φ l₂ := by
    intro l₁ l₂
    funext k
    simp only [φ, pullV, Matrix.mulVec, dotProduct, Pi.add_apply, map_add (f := _), mul_add, Finset.sum_add_distrib]
  have hzero : φ 0 = 0 := by
    funext k
    simp [φ, pullV, Matrix.mulVec, dotProduct]
  have hsmul : ∀ (c : 𝓞 D.host.E) l, φ (c • l) = (⟨_, hint c⟩ : intV D.host.E v) • φ l := by
    intro c l
    funext k
    set_option synthInstance.maxHeartbeats 100000 in
      simp only [φ, pullV, Matrix.mulVec, dotProduct, Pi.smul_apply, Subring.smul_def, smul_eq_mul, map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [show c • l j = (c : D.host.E) * l j from Algebra.smul_def c (l j), map_mul, map_mul, map_mul, map_mul, mul_left_comm]
    congr 1
  have hmem : ∀ l ∈ compan (sp := D.sp) (gramN D i hi) a (latAd x.1 lev.Lb), φ l ∈ M := by
    intro l hl
    obtain ⟨l₁, h₁, l₂, h₂, rfl⟩ := Submodule.mem_sup.1 hl
    rw [hadd]
    refine M.add_mem (GlobalTheory.T.placeComponent_pullback_latticeVector_mem_dual_span i hi lev x v l₁ h₁) ?_
    refine Submodule.smul_induction_on h₂ ?_ ?_
    · intro r hr s hs
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hr
      rw [hsmul]
      refine M.smul_mem _ ?_
      induction hs using Submodule.span_induction with
      | mem s hs => exact GlobalTheory.T.stepPoint_pulledDualVector_mem_localBaseLattice i hi lev x v s hs
      | zero => rw [hzero]; exact M.zero_mem
      | add p q _ _ hp hq => rw [hadd]; exact M.add_mem hp hq
      | smul c s _ h => rw [hsmul]; exact M.smul_mem _ h
    · intro p q hp hq
      rw [hadd]
      exact M.add_mem hp hq
  unfold latCo at hw
  obtain ⟨l, hl, rfl⟩ := Submodule.mem_map.1 hw
  refine ⟨⟨_, hmem l hl⟩, funext fun k => congrArg (prV (E := D.host.E) v) (congrFun ?_ k)⟩
  unfold pullV
  rw [_root_.mul_inv_rev, Units.val_mul, ← Matrix.mulVec_mulVec]
  congr 1
  funext j
  symm
  rw [LinearMap.restrictScalars_apply, LinearEquiv.coe_coe, toLE_apply, ← map_inv]
  show ((((crd⁻¹ : GL (Fin (D.R.N i)) D.host.E) : Matrix (Fin (D.R.N i)) (Fin (D.R.N i)) D.host.E).map (inclE (F := D.host.F) (Formalism.L2.Herm.Af D.host.F))) *ᵥ _) j = _
  refine (RingHom.map_mulVec _ _ _ j).symm.trans ?_
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]


set_option maxHeartbeats 1000000 in
theorem fnl_eq : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D} {cX : ExtraC}
    {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (dtU : (letI := D.host.cmStar; Formalism.L2.Herm.unitaryOneFiniteAdeles D.sp.cm) →* D.Dt) (a : 𝓞 D.host.E), AdPins A dtU → AdTie A dtU a →
    ∀ (i : ℕ) (hi : i ≤ D.R.m) (β : (St i hi).Ch) (x x₁ : UA D i hi) (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i),
    IsPtAd A a i hi β x p → IsPtAd A a i hi β x₁ p₁ → ∀ P : t.Pr.vT (t.word u),
    (∀ v : HeightOneSpectrum (𝓞 D.host.F), IsOver v (seamP t.seam P.1) → bc (prV (E := D.host.E) v) x₁.1 = bc (prV (E := D.host.E) v) x.1) →
    ∀ y ∈ p.deco.1.at P.1, p₁.deco.1.f P y = p.deco.1.f P y := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A dtU a hpin htie i hi β x x₁ p p₁ hp hp₁ P hagree y hy
  have hat := GlobalTheory.T.localizedLattice_eq_of_adelic_matrices_agree_at_place A dtU a hpin htie i hi β x x₁ p p₁ hp hp₁ P hagree
  set v := HeightOneSpectrum.under (𝓞 D.host.F) (seamP t.seam P.1) with hvdef
  have hvo : IsOver v (seamP t.seam P.1) := by
    unfold IsOver
    rw [hvdef, HeightOneSpectrum.under_asIdeal]
  have hTv : (((St i hi).T : ℕ) : 𝓞 D.host.F) ∈ v.asIdeal := by
    rw [htie.T_eq]
    exact T_mem_under t u P v hvo
  have hd := p.deco.2
  have hd₁ := p₁.deco.2
  obtain ⟨s, hs, hsy⟩ := (mem_locP P.1 _ y).1 hy
  have hy₁ : y ∈ p₁.deco.1.at P.1 := hat ▸ hy
  obtain ⟨s₁, hs₁, hsy₁⟩ := (mem_locP P.1 _ y).1 hy₁
  have hsP : s * s₁ ∉ P.1.asIdeal := fun h => (P.1.isPrime.mem_or_mem h).elim hs hs₁
  have hw : (s * s₁) • y ∈ p.deco.1.N := by
    rw [mul_comm, mul_smul]
    exact Submodule.smul_mem _ _ hsy
  have hw₁ : (s * s₁) • y ∈ p₁.deco.1.N := by
    rw [mul_smul]
    exact Submodule.smul_mem _ _ hsy₁
  have hlat : (fun l => t.seam.iE (((s * s₁) • y) l)) ∈
      latCo D.sp (gramN D i hi) (A.crd i hi) a x.1 ((St i hi).K β).lev.Lb := by
    rw [← hp.lat]
    exact Submodule.subset_span ⟨_, hw, rfl⟩
  obtain ⟨z, hz⟩ := exists_unit_one_add_generator i hi ((St i hi).K β).lev (A.crd i hi) a x v _ hlat
  have e1 := hp.fnl P v hTv hvo _ hw z hz
  have hz₁ : z.1 = fun l => prV (E := D.host.E) v (pullV (F := D.host.F) (ratA D.host.F (A.crd i hi) * x₁.1)
      (fun b => t.seam.iE (((s * s₁) • y) b)) l) := by
    have hbc : bc (prV (E := D.host.E) v) (ratA D.host.F (A.crd i hi) * x₁.1) =
        bc (prV (E := D.host.E) v) (ratA D.host.F (A.crd i hi) * x.1) :=
      ((MonoidHom.map_mul _ _ _).trans (congrArg (bc (prV (E := D.host.E) v) (ratA D.host.F (A.crd i hi)) * ·) (hagree v hvo))).trans
        (MonoidHom.map_mul _ _ _).symm
    refine hz.trans (funext fun l => ?_)
    exact (prV_pullV_congr (F := D.host.F) (E := D.host.E) v (ratA D.host.F (A.crd i hi) * x.1)
      (ratA D.host.F (A.crd i hi) * x₁.1) hbc (fun b => t.seam.iE (((s * s₁) • y) b)) l).symm
  have e2 := hp₁.fnl P v hTv hvo _ hw₁ z hz₁
  have f1 := hd.f_smul P (s * s₁) y hy
  have f2 := hd₁.f_smul P (s * s₁) y hy₁
  haveI := P.1.isPrime
  have hne : Ideal.Quotient.mk P.1.asIdeal (s * s₁) ≠ 0 := by
    rwa [Ne, Ideal.Quotient.eq_zero_iff_mem]
  apply mul_left_cancel₀ hne
  rw [← f1, ← f2, e1, e2]

end GlobalTheory.FnlAway
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointFramesMoveIntegralRightTranslateStatement
section
open NumberField IsDedekindDomain Matrix Formalism.BasicNotions Formalism.UG Formalism.L2.Col Formalism.L2.PairingIndexBounds.F Formalism.MainNotions.G.KAat Formalism.L2.Forms Formalism.L2.Ker Formalism.MainNotions Formalism.L2.DIV Formalism.MainNotions.G GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.chartPoint_frames_move_integralRightTranslate : UnderTie (fun {D L hT Gi Gl Kc Y cX ex t u μ St} A dtU a => ∀ (i : ℕ) (p : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i) (y k : SB t μ → GL (Fin (D.R.N i)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)), (∀ P : SB t μ, CongAt (seamP t.seam P.1) 0 (k P) ∧ CongAt (seamP t.seam P.1) 0 (k P)⁻¹) → (∀ P : SB t μ, NearAt (seamP t.seam P.1) ((t.cst μ).D P) (y P) (seamGL t.seam (frsF t.sel (t.tup μ) p P))) → ∃ p' : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) i, p'.deco.1.N = p.deco.1.N ∧ p'.deco.1.f = p.deco.1.f ∧ ∀ P : SB t μ, NearAt (seamP t.seam P.1) ((t.cst μ).D P) (y P * k P) (seamGL t.seam (frsF t.sel (t.tup μ) p' P))) := by
  first | exact @GlobalTheory.FrameShift.exists_pt_mul | exact GlobalTheory.FrameShift.exists_pt_mul | (intros; apply GlobalTheory.FrameShift.exists_pt_mul <;> assumption)
end

