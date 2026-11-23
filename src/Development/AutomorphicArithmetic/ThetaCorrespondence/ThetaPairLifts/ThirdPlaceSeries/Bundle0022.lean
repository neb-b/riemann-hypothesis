module

public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SideMultiplicityFamily
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeStableRationalLattice
public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0329
public import Development.AutomorphicArithmetic.Foundations.UnitarySphericalFixing.SatakeParameters.GoodAUIso
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0326
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.TiedColumnData

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HeckeOpenWithLoc
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.FitHecke
section NC
open Formalism.L2.NCov Module Module.End
variable {O K V : Type*} [CommRing O] [Field K] [Algebra O K]
  [AddCommGroup V] [Module K V] [Module O V] [IsScalarTower O K V] [IsLocalRing O] {S : Set (End K V)}
end NC
section Conj
variable {R : Ranks}
end Conj
section Gen
variable {D : D7} {M : MtFam D}
end Gen
section Chars
open Formalism.L2.Host
end Chars
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem heckeOpen_withLoc_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C), ChoiceSide D cf M Bs.exp C tp → MtInput D M tp.tup C.Q → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → (∀ j g, ∃ z : ℤ, eExp D j g = z) → (∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) → GlobalTheory.RowTie.ChebSplit D.nd → ∀ (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)) (Sp : NdSpec A.pl M C big L.X L.T) (Au : _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tp.tup Sp.iq L.Y L.C), ∃ Hk : _root_.GlobalTheory.HeightCounting.HeckeOpenStatements (withLoc L) (mtL L M) tp.tup, ∀ j h1 h2 π, Hk.au.cls j h1 h2 π = A.au.cls j h1 h2 π := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCh hMt hstar hexp hsplit hcheb big L Sp Au
  have hjf : ∀ i : L.X.Loc, L.X.j i - 1 + 1 = L.X.j i := fun i => by have := L.X.j_range i; omega
  let jf : L.X.Loc → Fin D.R.m := fun i => ⟨L.X.j i - 1, by have := L.X.j_range i; omega⟩
  let cover : NormalizedLocalCompatibility (withLoc L) (mtL L M) :=
    { B := { Sp.B with }
      Q_eq := Sp.Q_eq
      mx := Sp.mx
      mx_max := Sp.mx_max
      mx_inj := Sp.mx_inj
      mx_all := Sp.mx_all
      phO := Sp.phO
      phK := Sp.phK
      phK_alg := Sp.phK_alg
      phK_emb := Sp.phK_emb
      Psi := Sp.Psi
      Psi_inj := Sp.Psi_inj
      Psi_range := Sp.Psi_range
      Psi_pr := Sp.Psi_pr
      ptX := Sp.ptX
      ptX_hT := Sp.ptX_hT
      iotaC := Sp.iotaC
      iotaC_coh := fun j w i h z => by
        have e1 : (withLoc L).naut.iotaQ i = Sp.iq i := Au.iotaQ i
        have e2 : (withLoc L).naut.iotaQC i = qCast ((withLoc L).nd.w_l i) (A.pl.ι ((withLoc L).nd.w i)) := Au.iotaQC i
        unfold iotaOC
        rw [RingHom.comp_apply, RingHom.comp_apply, e1, e2]
        exact Sp.iotaC_coh j w i h z }
  have hstd : HeckeStd cover.B := Sp.std
  refine ⟨{ hecke := ?_, av := { S := Au.S, irr := Au.irr, inj := Au.inj, surj := Au.surj, typeV := Au.typeV, ptV := Au.ptV }, au := { A.au with }, emb := Au.emb, rational := rational_of cover, level := ?_, data := { bj := Sp.bj, bj_span := Sp.bj_span, bj_rel := fun i c => Sp.bj_rel i (sOf _ i) (sOf_spec _ i) c }, cover := cover }, fun j h1 h2 π => rfl⟩
  · refine { J_hyp := fun i => ?_
             hT := hT_of cover hstd Sp.act_hK
             sameO := sameO_of cover
             sep := sep_of cover hstd
             Q_conj := Q_conj_of cover
             Q_same := Q_same_of cover fun j j' w => (Sp.Qc_eq j w).trans (Sp.Qc_eq j' w).symm }
    have h0 := hMt.hyp (L.X.w i) (jf i)
    have h1 := hypOutside_transport' (M := M) (L.X.mu_w i).symm (hjf i) _ _ (L.X.j_range i).1 (L.X.j_range i).2 _ h0
    refine hypOutside_mono (D := withLoc L) _ _ ?_ h1
    have hi := mem_locs_self (D := withLoc L) i
    have hQe : C.Q (L.X.w i) = L.X.Q i := ((Sp.Q_eq _ _ i hi).trans (Sp.Qc_eq _ _)).symm
    intro v hv
    rcases hv with hv | hv
    · exact gPl_sub_badPl (D := withLoc L) i hv
    · obtain ⟨w', hov, hw'⟩ := qPl_sub tp (L.X.w i) (L.X.w_tw i) (jf i) hv
      refine ⟨w', hov, ?_⟩
      rcases hw' with hQ | hp
      · left
        rw [hQe] at hQ
        exact hQ
      · right; right
        rw [L.X.w_l i] at hp
        exact hp
  · refine { prod := ?_, para := ?_, uni := ?_, wt := ?_, hyp := ?_ }
    · exact fun i => mt_transport M (fun μ j m => NG.IsProdLevel m.J) (L.X.mu_w i).symm (hjf i) _ _ _ _
        (hMt.prod (L.X.w i) (jf i))
    · exact fun i j hj => mt_transport M (fun μ jj m => ∀ v ∈ qPl D (tp.tup μ j),
        ∃ (s : SplitPlace D.host.E) (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), s.v = v ∧
          NG.IsCompAt (tp.tup μ j) s ξ ∧ NG.LevelPara m.J m.χ s D.R.r ξ) (L.X.mu_w i).symm hj _ _ _ _
        (hMt.para (L.X.w i) j)
    · exact fun i j hj => mt_transport M (fun μ jj m => ∀ (k : Fin 2) (v : D.nd.PlG k) (s : SplitPlace D.host.E),
        s.w = D.naut.plGw k v → ∃ (ψ₀ : AddChar (s.v.adicCompletion (maximalRealSubfield D.host.E)) ℂ)
          (ξ : (s.v.adicCompletion (maximalRealSubfield D.host.E))ˣ →* ℂˣ), NG.IsPsi0 s ψ₀ ∧
          NG.IsCompAt (tp.tup μ j) s ξ ∧ NG.LevelUni m.J m.χ s D.R.r ψ₀ ξ) (L.X.mu_w i).symm hj _ _ _ _
        (hMt.uni (L.X.w i) j)
    · intro μ j t sh a lam hinf hdual hhw
      have e := infG_etaT A.chr t
      have hsh : sh = 1 / 2 := by
        have := Multiset.singleton_inj.1 (hinf.symm.trans e)
        rw [this]; push_cast; ring
      rw [hsh]
      exact hMt.wt μ j t a lam hdual hhw
    · exact fun i j hj => mt_transport M (fun μ jj m => NG.HypOutside m.J m.χ (gPl D ∪ qPl D (tp.tup μ j)))
        (L.X.mu_w i).symm hj _ _ _ _ (hMt.hyp (L.X.w i) j)
end GlobalTheory.FitHecke
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.HkStabAll
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.HeightCounting.HeckeLat
end GlobalTheory.HeightCounting.HeckeLat
open GlobalTheory.HeightCounting.HeckeLat in
theorem GlobalTheory.HeightCounting.FormsStep.hkStab_of_ringSpec_of_subset : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) → HkStab D T S In := by
  intro D cf jE A S In b0 b1 Sx T Sp hSb _ i j b k P ⟨h1, h2, hk1, hk2, hsp, hP⟩ x hx
  obtain ⟨Φ, hc, hf, hw, hint, W0, hW0, hW0c, hrel⟩ := descend_integral D T S In i j b h1 h2
  have ha := descend_actL D T S In i j b h1 h2 Φ hc hf
  have he := descend_eSum D T S In i j b Φ hc ha
  have hPb : P ∉ In.Sb := fun h => hP (by
    rw [← Finset.mem_coe, Sp.ringSpec_excludedPlaces_eq i]
    exact Or.inr (Finset.mem_coe.mpr (hSb h)))
  have hMW : ∀ y ∈ (S.A j).MK, y ∈ WKr D S j := fun y hy => by
    rw [WKr_of D S h1 h2]; exact hy.1
  have hML : ∀ y ∈ Submodule.span (𝓞 D.what₂.LL) ((S.A j).MK : Set (S.WL j)), Φ y ∈ BsupT D T S i j b := by
    have key : ∀ y ∈ Submodule.span (𝓞 D.what₂.LL) ((S.A j).MK : Set (S.WL j)), ∀ a : 𝓞 D.what₂.LL,
        Φ (a • y) ∈ BsupT D T S i j b := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        intro a
        obtain ⟨o, ho⟩ := hint a ⟨y, hMW y hy⟩
        rw [← algebraMap_smul D.what₂.LL a y]
        refine ho ▸ Submodule.smul_mem _ o ?_
        exact Submodule.subset_span ⟨⟨y, hMW y hy⟩, hy, hw _⟩
      | zero => intro a; rw [smul_zero, map_zero]; exact zero_mem _
      | add y z _ _ hy hz => intro a; rw [smul_add, map_add (f := _)]; exact add_mem (hy a) (hz a)
      | smul a' y _ hy => intro a; rw [smul_smul]; exact hy _
    intro y hy
    simpa using key y hy 1
  have hhr : ∀ w : ↥(WKr D S j), (hLr D S In j k P w : S.WL j) = In.hL j k P w := by
    intro w
    unfold hLr
    rw [dite_eq_left ⟨h1, h2⟩]
    rfl
  have hkΦ : ∀ y, hkT D T S In i j b k P (Φ y) = ((cHkT D T i b P : T.O i) ^ k) • Φ (In.hL j k P y) := by
    intro y
    rw [← algebraMap_smul (FractionRing (T.O i)), map_pow, hf _ _ hhr]
    rfl
  obtain ⟨n, hn⟩ := In.hL_int j k P h1 h2 hsp hPb hk2
  obtain ⟨u, hu⟩ := (normV_isUnit D T i P hP).pow n
  have hstep : ∀ y ∈ Submodule.span (𝓞 D.what₂.LL) ((S.A j).MK : Set (S.WL j)), y ∈ goodL D S In.θ j →
      hkT D T S In i j b k P (Φ y) ∈ BI D T S In i j b := by
    intro y hy hg
    rw [hkΦ]
    refine Submodule.smul_mem _ _ ⟨?_, ?_⟩
    · have h3 := hML _ (hn y hy hg)
      rw [map_nsmul, ← Nat.cast_smul_eq_nsmul (T.O i), Nat.cast_pow, ← hu] at h3
      have h4 := Submodule.smul_mem _ (↑u⁻¹ : T.O i) h3
      rwa [smul_smul, Units.inv_mul, one_smul] at h4
    · exact descend_mem_V0T D T S In i j b Φ hc ha he _ (hL_goodL D S In j k P h1 h2 ⟨hk1, hk2, hsp, hPb⟩ y hg)
  have hET : ∀ a y, Φ (eqL D S In.θ j a y) = eqT D T S In i j b a (Φ y) := by
    intro a y
    cases a with
    | none => simp only [eqL, eqT, LinearMap.sub_apply, Module.End.one_apply, map_sub, he]
    | some u =>
      simp only [eqL, eqT, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, ha, hc,
        LinearEquiv.coe_coe]
  have hx0 : ∀ a, eqT D T S In i j b a x = 0 := by
    intro a
    have h3 := goodTwistSideForms_le_span_goodLiftForms D S In T i j b h1 h2 (eIdem_all D) Φ hc ha he hw hx.2
    refine (Submodule.span_le (p := LinearMap.ker (eqT D T S In i j b a))).mpr ?_ h3
    rintro _ ⟨y, hy, rfl⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, ← hET, (mem_goodL_iff D S In.θ j y).mp hy a, map_zero]
  obtain ⟨m, o, g, rfl⟩ := Submodule.mem_span_set'.mp hx.1
  choose w hwM hwg using fun t => (g t).2
  have hg : ∀ t, (g t : FmT D T S i j b) = Φ (w t) := fun t => (hwg t).trans (hw _).symm
  simp only [hg] at hx0 ⊢
  haveI : Fintype ↥(Formalism.IndefR.NX.U D.nd) := Fintype.ofFinite _
  have hsol := hrel (fun t a => eqL D S In.θ j a (w t)) (fun t a => eqL_rational D S In j h1 h2 W0 hW0 hW0c a (w t)) o (by
    intro a
    set_option synthInstance.maxHeartbeats 100000 in
      rw [← hx0 a, map_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [hET, LinearMap.map_smul_of_tower])
  clear hx0 hx
  induction hsol using Submodule.span_induction with
  | mem o ho =>
    obtain ⟨c, hc0, hco⟩ := ho
    have h3 : ∑ t, o t • Φ (w t) = Φ (∑ t, ((c t : ↥D.LL0) : D.what₂.LL) • (w t : S.WL j)) := by
      set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      refine Finset.sum_congr rfl fun t _ => ?_
      rw [hc, ← hco, algebraMap_smul]
    rw [h3]
    refine hstep _ (Submodule.sum_mem _ fun t _ => ?_) ((mem_goodL_iff D S In.θ j _).mpr fun a => ?_)
    · let a : 𝓞 D.what₂.LL := ⟨((c t : ↥D.LL0) : D.what₂.LL),
        (RingOfIntegers.isIntegral_coe (c t)).map (algebraMap ↥D.LL0 D.what₂.LL).toIntAlgHom⟩
      have h4 := Submodule.smul_mem _ a (Submodule.subset_span (R := 𝓞 D.what₂.LL) (s := ((S.A j).MK : Set (S.WL j))) (hwM t))
      rwa [← algebraMap_smul D.what₂.LL a] at h4
    · set_option synthInstance.maxHeartbeats 100000 in
        rw [map_sum]
      simpa only [map_smul] using hc0 a
  | zero => simp
  | add o o' _ _ ho ho' =>
    simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib, map_add (f := _)]
    exact add_mem ho ho'
  | smul r o _ ho =>
    simp only [Pi.smul_apply, smul_eq_mul, mul_smul, ← Finset.smul_sum, LinearMap.map_smul_of_tower]
    exact Submodule.smul_mem _ _ ho
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LocBrOfAutSpec
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem locBr_of_autSpec_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E), ∀ (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T), ∀ (Y : LocAut X) (Cb : LocBC Y), _root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tup Sp.iq Y Cb → ∃ Br : LocBr Y, Br.nbr = Sp.nbr := by
  intro D cf jE A M C tup big X T Sp Y Cb hA
  refine ⟨⟨Sp.nbr, Sp.nbr_ind, Sp.self_good, ?_⟩, rfl⟩
  intro i w hw
  have hφ : ∀ x : X.nd.O i, iotaOQ X.nd Y.naut i x =
      (((Sp.nbr i w hw).toLL x : ↥(Sp.nbr i w hw).LL.1) : Loc.Om (X.nd.l i)) := by
    intro x
    show Y.naut.iotaQ i (algebraMap _ _ x) = _
    rw [hA.iotaQ i]
    exact Sp.nbr_iq i w hw x
  have hL := A.wd.loc (X.nd.l i) (Y.naut.iotaQC i) w hw (X.nd.O i) (Sp.nbr i w hw) (Sp.nbr_ind i w hw)
    (iotaOQ X.nd Y.naut i) hφ
  refine ⟨hφ, ?_, ?_⟩
  · intro m ρ hρ
    obtain ⟨h1, h2, h3, h4⟩ := hL.1 m ρ hρ
    obtain ⟨-, e1, e2, e3, e4⟩ := hA.wdOf i m (mapRep (iotaOQ X.nd Y.naut i) ρ) w
    refine ⟨e1.trans h1, e3.trans h2, e2.trans h3, ?_⟩
    intro τ τ' hτ
    rw [show Y.naut.jumpsW i (mapRep (iotaOQ X.nd Y.naut i) ρ) τ = _ from e4 τ]
    exact h4 τ τ' hτ
  · intro LL' hLL m ρ hρ
    obtain ⟨h1, h2, h3, h4⟩ := hL.2 LL' hLL m ρ hρ
    obtain ⟨-, e1, e2, e3, e4⟩ := hA.wdOf i m (mapRep (algebraMap ↥LL'.1 (Qbar (X.nd.l i))) ρ) w
    refine ⟨e1.trans h1, e3.trans h2, e2.trans h3, ?_⟩
    intro τ τ' hτ
    rw [show Y.naut.jumpsW i (mapRep (algebraMap ↥LL'.1 (Qbar (X.nd.l i))) ρ) τ = _ from e4 τ]
    exact h4 τ τ' hτ
end GlobalTheory.HeightCounting
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.MLocVUnr
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.AutUnr
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem locV_unr_m_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (ι : Type) [Finite ι] (F : ι → Submodule ℂ (GAf D.host.E D.R.nV → (mlX M X i).wt.W)) (irr : ∀ P, NG.IsIrrRep (mlX M X i).wt.ρ (F P)) (hinj : ∀ P P', NG.IsoRep (F P) (F P') → P = P') (hsurj : ∀ S', NG.IsIrrRep (mlX M X i).wt.ρ S' → (NG.isoTyp (mlX M X i).wt.ρ S').comap (mlX M X i).real ≠ ⊥ → ∃ P, NG.IsoRep (F P) S') (hne : ∀ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real ≠ ⊥) (hind : iSupIndep (fun P => (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real)) (htop : ⨆ P, (NG.isoTyp (mlX M X i).wt.ρ (F P)).comap (mlX M X i).real = ⊤) (P : ι) (w : PlE D.host), IsSplitPl D.host w → w ∉ X.nd.Q i → (∀ k, w ∉ placesOver D.host.E (D.host.g k)) → w ∉ placesOver D.host.E (if X.nd.l i = D.host.pde then D.host.pde' else D.host.pde) → D.naut.unr (D.nbc.locAU (X.nd.j i) (A.au.cls (X.nd.j i) (X.nd.j_range i).1 (X.nd.j_range i).2 { (mlX M X i).wt with S := F P, irrS := irr P }) w) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i ι _ F irr hinj hsurj hne hind htop P w hw hQ hg hp
  classical
  obtain ⟨s, hsw⟩ := exists_splitPlace_eq D w hw
  have hov : NG.OverPl w s.v := hsw ▸ s.w_under
  have hjf : X.nd.j i - 1 + 1 = X.nd.j i := by have := X.nd.j_range i; omega
  let jf : Fin D.R.m := ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩
  have h0 := hMI.hyp (X.nd.w i) jf
  have hyp : NG.HypOutside (mlX M X i).J (mlX M X i).χ (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf)) :=
    GlobalTheory.FitHecke.hypOutside_transport' (M := M) (X.nd.mu_w i).symm hjf _ _ (X.nd.j_range i).1 (X.nd.j_range i).2 _ h0
  have hi : i ∈ X.nd.locs (X.nd.j i) (X.nd.w i) := (X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  have hQe : C.Q (X.nd.w i) = Sp.B.Qc (X.nd.j i) (X.nd.w i) := (Sp.Qc_eq _ _).symm
  have hvB : s.v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf) := by
    rintro (⟨w', hov', k, hk⟩ | hq)
    · exact hg k (mem_placesOver_of_overPl hov hov' hk)
    · obtain ⟨w', hov', hw'⟩ := GlobalTheory.FitHecke.qPl_sub tp (X.nd.w i) (X.nd.w_tw i) jf hq
      rcases hw' with hQ' | hp'
      · rw [hQe] at hQ'
        have hwQ : w ∈ Sp.B.Qc (X.nd.j i) (X.nd.w i) := Sp.B.Qc_over _ _ w' w hQ' ⟨s.v, hov', hov⟩
        rw [← Sp.Q_eq _ _ i hi] at hwQ
        exact hQ hwQ
      · rw [X.nd.w_l i] at hp'
        exact hp (mem_placesOver_of_overPl hov hov' hp')
  obtain ⟨y, hy, hy0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot (hne P)
  have hfix : ∀ κ ∈ {κ : GAf D.host.E D.R.nV | κ ∈ Umax D.host.E D.R.nV ∧ TrivOutside {s.v} κ},
      NG.rt D.host.E D.R.nV κ ((mlX M X i).real y) = (mlX M X i).real y := by
    rintro κ ⟨hU, htr⟩
    have htr' : TrivOutside (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf))ᶜ κ := by
      intro v hv
      apply htr v
      rintro rfl
      exact hv hvB
    obtain ⟨hJ, hχ⟩ := hyp κ htr'
    have hκ : κ ∈ (mlX M X i).J := hJ.2 hU
    have hmem : (mlX M X i).real y ∈ NG.TypeSp (mlX M X i).wt.ρ (mlX M X i).J (mlX M X i).χ := by
      rw [← (mlX M X i).real_range]; exact ⟨y, rfl⟩
    have e := hmem.2 ⟨κ, hκ⟩
    rw [hχ hκ] at e
    simpa using e
  have hr0 : (mlX M X i).real y ≠ 0 := fun h =>
    hy0 ((mlX M X i).real_inj (h.trans (map_zero _).symm))
  obtain ⟨f, hf, hf0, hff⟩ := exists_fixed_of_isoTyp (mlX M X i).wt.ρ (irr P).1.stable _ hy hr0 hfix
  have hsph : _root_.UpperTheory.One.M.SphAtG { (mlX M X i).wt with S := F P, irrS := irr P } s.v :=
    _root_.UpperTheory.One.M.New.sphMk ⟨f, hf, hf0, fun κ hU htr => hff κ ⟨hU, htr⟩⟩
      fun h => absurd rfl (h s)
  rw [← hsw]
  exact A.au.locUnr _ _ _ _ s hsph
end GlobalTheory.AutUnr
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.NRhoTiedWithLoc
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting.FitRho
open Formalism.L2.NR
end GlobalTheory.HeightCounting.FitRho
namespace GlobalTheory.HeightCounting.FitRho
open Formalism.L2.NR
end GlobalTheory.HeightCounting.FitRho
namespace GlobalTheory.HeightCounting.FitRho
open Formalism.L2.NR
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem rhoS_withLoc_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D')
    (hcheb : GlobalTheory.RowTie.ChebSplit b.D.nd) (hP : RowPar (withLoc b.L)) (hG : GalRepEx (withLoc b.L))
    (hC : ClassFieldHeckeAlgebraic (withLoc b.L)) (hη : EtaShiftInt (withLoc b.L)) (a : (withLoc b.L).nd.Loc)
    (s : (withLoc b.L).ntw.Sig ((withLoc b.L).ntw.twOf a))
    (hs : (withLoc b.L).ntw.side _ s = (withLoc b.L).ntw.twSide a) (hj : (withLoc b.L).ntw.jS _ s = (withLoc b.L).nd.j a) :
    ∃ (σ : (withLoc b.L).what₂.FT) (hσ : (withLoc b.L).what₂.isot ((withLoc b.L).nd.j a) σ ≠ ⊥)
      (hg : (withLoc b.L).nd.goodRow σ),
      ∀ (π : (withLoc b.L).naut.CG (withLoc b.L).R.r) (hS : rowSig (withLoc b.L) a σ = [⟨(withLoc b.L).R.r, π, 1⟩]),
        IsConjRep (Formalism.MainNotions.N.mapRep ((Formalism.MainNotions.N.iotaOQ (withLoc b.L).nd (withLoc b.L).naut a).comp ((withLoc b.L).ntw.twist₂ a))
            ((withLoc b.L).ntw.rhoS _ s))
          (rhoOfRow (withLoc b.L) hG hC hη a π (rowSig_csd_ralg (withLoc b.L) hP a σ hσ hg π hS).1
            (rowSig_csd_ralg (withLoc b.L) hP a σ hσ hg π hS).2) := by
  obtain ⟨hiso, hgood, hspec⟩ := b.Bs.rhoS (b.L.T.twOf a) s
  have hσ : (withLoc b.L).what₂.isot ((withLoc b.L).nd.j a) (b.Bs.rowS (b.L.T.twOf a) s) ≠ ⊥ := by
    rw [← hj]; exact hiso
  refine ⟨b.Bs.rowS (b.L.T.twOf a) s, hσ, hgood, fun π hS => ?_⟩
  obtain ⟨hc, hr⟩ := rowSig_csd_ralg (withLoc b.L) hP a _ hσ hgood π hS
  have hloc : ∀ w, IsSplitPl b.D.host w → b.D.naut.locG π w = b.A.row.locR (b.Bs.rowS (b.L.T.twOf a) s) w := by
    intro w hw
    have h1 := (rowSig_spec (withLoc b.L) hP a _ hσ).2.2 w hw
    rw [hS] at h1
    exact ((isoLoc_single (withLoc b.L) π w).symm.trans h1).trans (b.Au.locW a _ w)
  have hpq : (withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a) = (withLoc b.L).nd.l a := (withLoc b.L).ntw.twOf_l a
  let φ0 : FractionRing ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) →+* Qbar ((withLoc b.L).nd.l a) :=
    ((withLoc b.L).naut.iotaQ a).comp (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap ((withLoc b.L).ntw.twist₂ a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.twO_inj (withLoc b.L).ntw a))
  have hφ0 : φ0.comp (algebraMap ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) (FractionRing ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)))) =
      (Formalism.MainNotions.N.iotaOQ (withLoc b.L).nd (withLoc b.L).naut a).comp ((withLoc b.L).ntw.twist₂ a) := by
    ext y
    show (withLoc b.L).naut.iotaQ a (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap _ _ (algebraMap _ _ y)) =
      (withLoc b.L).naut.iotaQ a (algebraMap _ _ ((withLoc b.L).ntw.twist₂ a y))
    rw [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg]
  have hemb : ∀ x : ↥b.D.LL0, GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap ((withLoc b.L).ntw.twist₂ a) (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.twO_inj (withLoc b.L).ntw a)
      ((if (withLoc b.L).ntw.twSide a then (withLoc b.L).ntw.emb0 ((withLoc b.L).ntw.twOf a) else (withLoc b.L).ntw.emb0b ((withLoc b.L).ntw.twOf a)) x) =
      (withLoc b.L).nd.embK a (x : b.D.what₂.LL) :=
    fracMap_eq ((withLoc b.L).ntw.twist₂ a) _ (if (withLoc b.L).ntw.twSide a then (withLoc b.L).ntw.emb0 ((withLoc b.L).ntw.twOf a) else (withLoc b.L).ntw.emb0b ((withLoc b.L).ntw.twOf a))
      (((withLoc b.L).nd.embK a).comp (algebraMap ↥b.D.LL0 b.D.what₂.LL)) (fun x y hy => (withLoc b.L).ntw.twO_emb a x y hy)
  let φ := (castQ hpq).symm.toRingHom.comp φ0
  let ι := (castQ hpq).trans ((withLoc b.L).naut.iotaQC a)
  have hφ : ∀ z : ℤ_[(withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a)], φ (algebraMap ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) (FractionRing ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a))) (algebraMap ℤ_[(withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a)] ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) z)) =
      algebraMap ℚ_[(withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a)] (Qbar ((withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a))) (z : ℚ_[(withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a)]) := by
    intro z
    obtain ⟨z', hz⟩ := exists_heq hpq z
    show (castQ hpq).symm ((withLoc b.L).naut.iotaQ a (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap _ _ (algebraMap ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) (FractionRing ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a))) (algebraMap ℤ_[((withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a))] ((withLoc b.L).ntw.O0 ((withLoc b.L).ntw.twOf a)) z)))) = _
    rw [GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap_alg]
    erw [b.Sp.twO_alg a z z' hz, (withLoc b.L).naut.iotaQ_alg a z']
    exact castQ_alg hpq z z' hz
  have hι : ∀ x : ↥b.D.LL0, ι (φ ((if (withLoc b.L).ntw.side ((withLoc b.L).ntw.twOf a) s then (withLoc b.L).ntw.emb0 ((withLoc b.L).ntw.twOf a)
      else (withLoc b.L).ntw.emb0b ((withLoc b.L).ntw.twOf a)) x)) = embLL0 b.D x := by
    intro x
    have hs' : (withLoc b.L).ntw.side ((withLoc b.L).ntw.twOf a) s = (withLoc b.L).ntw.twSide a := hs
    rw [hs']
    show (withLoc b.L).naut.iotaQC a ((castQ hpq) ((castQ hpq).symm ((withLoc b.L).naut.iotaQ a (GlobalTheory.IndefiniteRowSideFullHecke.LatticeConditions.fracMap _ _ _)))) = _
    rw [RingEquiv.apply_symm_apply, hemb x]
    exact (withLoc b.L).naut.iota_LL a _
  have hR := hspec π hc hr hloc φ ι hφ hι
  have hR' : IsRepOf (withLoc b.L) ((withLoc b.L).ntw.l ((withLoc b.L).ntw.twOf a)) ((castQ hpq).trans ((withLoc b.L).naut.iotaQC a))
      ((withLoc b.L).naut.tw π (withLoc b.L).naut.etaTinv) ((1 - ((withLoc b.L).R.nV : ℝ)) / 2)
      (Formalism.MainNotions.N.mapRep (castQ hpq).symm.toRingHom (Formalism.MainNotions.N.mapRep
        ((Formalism.MainNotions.N.iotaOQ (withLoc b.L).nd (withLoc b.L).naut a).comp ((withLoc b.L).ntw.twist₂ a))
        ((withLoc b.L).ntw.rhoS _ s))) := by
    rw [← hφ0, mapRep_mapRep]
    exact hR
  exact conj_of_isRepOf (withLoc b.L) ((withLoc b.L).naut.iotaQC a) _ _ hcheb _ _
    (isRepOf_cast (withLoc b.L) hpq _ _ _ _ hR') (rhoOfRow_isRepOf (withLoc b.L) hG hC hη a π _ _)
end GlobalTheory.HeightCounting.FitRho
namespace GlobalTheory.HeightCounting
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem nRhoTied_withLoc_alt : ∀ (hL : _root_.UpperTheory.Zero.LLC.RecTExists) (D' : D7) (b : _root_.GlobalTheory.HeightCounting.NormChoiceConstructed hL D'), (∀ x : b.D.LL0, star (x : b.D.what₂.LL) ∈ b.D.LL0) → (∀ j g, ∃ z : ℤ, eExp b.D j g = z) → (∀ v, v ∈ placesOver b.D.host.E b.D.host.pde ∨ v ∈ placesOver b.D.host.E b.D.host.pde' → IsSplitPl b.D.host v) → GlobalTheory.RowTie.ChebSplit b.D.nd → TypesOpen (withLoc b.L) b.jE → NR.NRhoTied (withLoc b.L) := by
  intro hL D' b _ _ _ hcheb hT
  exact ⟨hT.rbarSS, hT.rbar, fun hP hG hC hη a s hs hj =>
    _root_.GlobalTheory.HeightCounting.FitRho.rhoS_withLoc_alt hL D' b hcheb hP hG hC hη a s hs hj⟩
end GlobalTheory.HeightCounting
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShHalf
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
namespace GlobalTheory.EtaTildeShift
theorem sh_half_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (t : D.what₂.Tau) (sh : ℂ),
    D.naut.infG D.naut.etaT (embT D t) = {sh} → ∃ z : ℤ, sh = (z : ℂ) + 1 / 2 := by
  intro D cf jE A t sh h
  have hE : (A.chr.e1 D.naut.etaT).1.HasInfQ (embPsi D.host) (fun _ => (1 / 2 : ℚ)) :=
    ⟨fun _ => 1, fun _ => by norm_num, by rw [A.chr.etaT]; exact cf.isEta.inf⟩
  have h2 := (A.chr.infG _ _ hE (D.eTau t)).1
  have h3 : D.naut.infG D.naut.etaT (embT D t) = {((1 / 2 : ℚ) : ℂ)} := h2
  rw [h3] at h
  have := (Multiset.singleton_inj.1 h).symm
  refine ⟨0, ?_⟩
  rw [this]; push_cast; ring
end GlobalTheory.EtaTildeShift
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.TieOfTrue
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.Host GlobalTheory.Mem GlobalTheory.Mem.Col2 GlobalTheory.Mem.Top GlobalTheory.Mem.Top.Bl GlobalTheory.HeightCounting NumberField IsDedekindDomain
attribute [local instance] Formalism.BasicNotions.Host.cmStar
namespace GlobalTheory.HeightCounting.NchAt
set_option maxHeartbeats 4000000 in
theorem tie_of_true_alt {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D' : D7} {cf' : CharFrame D'} {C' : NChoice D'} {tp' : TupTied D' cf' C'}
    (b : _root_.GlobalTheory.HeightCounting.NormChoiceRealisation hL D' cf' C' tp') : NChTie D' C' ∧ PsiChoiceCompatible D' cf' C' tp' := by
  obtain ⟨⟨D, cf, jE, A, cg, au, rep, row, low, Pq, S, hL', eig, θ, Bs, M, C, tp, ch, mt, big, L, Sp, Au, ss, eq⟩, pack⟩ := b
  subst eq
  cases pack
  refine ⟨⟨Sp.twOf_eq, Sp.twSide_eq, fun a => ?_, ?_, ch.nct.embedding_baseField_condition⟩, ch.psi⟩
  · exact (Sp.Q_eq _ _ a (((L.X.nd.locs_mem _ _ a).2 ⟨rfl, rfl⟩))).trans (Sp.Qc_eq _ _)
  · obtain ⟨ψ0, hc, hw, -⟩ := ch.nct.psi_eq
    exact ⟨ψ0, hc, hw, fun a g => Sp.psi_eq a g _ (hw _ g)⟩
end GlobalTheory.HeightCounting.NchAt
end
end

