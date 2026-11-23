module

public import Mathlib
public import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
public import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0322
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0019
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0321
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0030
public import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Bundle0001
public import Development.AutomorphicArithmetic.Foundations.LocalLanglands.IsRecTOfIsRec
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0341
public import Formalism.LocalToGlobal.UnitaryNorms.Bundle0008
public import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ContinuousNormFin
public import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0029
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0351
public import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0334

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiMuFrobAll
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
open Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR GlobalTheory.HeckeGal
namespace GlobalTheory.ChiMuArtin
theorem chiMu_frob_all_alt : ∀ (hArt : GlobalTheory.Published.GlobalArtinReciprocity) (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (j : Fin D.R.m), j.1 + 1 = X.nd.j i → (∃ Bf : Finset (HeightOneSpectrum (𝓞 D.host.E)), ∀ P ∉ Bf, (tp.tup (X.nd.mu i) j * cf.eta⁻¹).UnrAt P ∧ ∀ σ : Formalism.ConjugateSelfDual.G D.host.E X.nd.Om, IsFrob (F := D.host.E) (X.nd.plOm.1 P) (normV P) σ → (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)) ((X.nd.chi i 1 σ : (X.nd.O i)ˣ) : X.nd.O i))) = (((tp.tup (X.nd.mu i) j * cf.eta⁻¹).val P)⁻¹ : ℂˣ).1 * ((normV P : ℕ) : ℂ) ^ (((((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) : ℝ) : ℂ)) → ∀ w, SplitOut X.nd i w → ∀ (B : ValuationSubring X.nd.Om) (σ : Formalism.ConjugateSelfDual.G D.host.E X.nd.Om), IsPlaceOver (F := D.host.E) B w → IsFrob (F := D.host.E) B (normV w) σ → (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)) ((X.nd.chi i 1 σ : (X.nd.O i)ˣ) : X.nd.O i))) = (((tp.tup (X.nd.mu i) j * cf.eta⁻¹).val w)⁻¹ : ℂˣ).1 * ((normV w : ℕ) : ℂ) ^ (((((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) : ℝ) : ℂ) := by
  intro hArt D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i j hj hae w hw B σ hB hσ
  obtain ⟨Bf, hBf⟩ := hae
  obtain ⟨art, ha⟩ := hArt D.host.E X.nd.Om
  let C' : GlobalTheory.Mem.Chr.HFrame D.host (eExp D) :=
    ⟨cf.P, cf.W, cf.mu0, cf.eta, cf.chiPsi, cf.del, cf.del', cf.isMu0, cf.isEta, cf.isChi, cf.isDel, cf.isDel'⟩
  obtain ⟨n0, h0⟩ := GlobalTheory.GalChar.exists_isAlgPos_mu0 C' hE j
  obtain ⟨m, hm0, hm⟩ := tp.xi_fin (X.nd.mu i)
  have hxa : IsAlgPos (tp.xi (X.nd.mu i)) 0 := isAlgPos_zero_of_orderDvd hm0 hm
  obtain ⟨n, hn⟩ := GlobalTheory.GalChar.block_alg C' ⟨_, GlobalTheory.GalChar.isAlgPos_mul h0 hxa⟩
  have hn' : IsAlgPos (GlobalTheory.GalChar.block (tp.tup (X.nd.mu i) j) cf.eta D.R.r) n := hn
  set ι := qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i)) with hι
  obtain ⟨r, hr, hLr⟩ := ha.exists_isLAdicOf ι hn'
  have hO := X.nd.O_adic i
  have hκ := Sp.iq_alg i
  have hρ : Continuous (GlobalTheory.GalChar.inQ (Sp.iq i) (X.nd.chi i 1)) :=
    GlobalTheory.GalChar.continuous_units _ ((GlobalTheory.GalChar.isEmbedding_toQ hO hκ).continuous.comp (X.nd.chi_cont i 1))
  have hlne : X.nd.l i ≠ 0 := (Fact.out : (X.nd.l i).Prime).ne_zero
  have hub : ∀ v, (tp.tup (X.nd.mu i) j * cf.eta⁻¹).UnrAt v →
      (GlobalTheory.GalChar.block (tp.tup (X.nd.mu i) j) cf.eta D.R.r).UnrAt v := by
    intro v hv x hx
    rw [GlobalTheory.GalChar.block_loc (cf.isEta.unr v) hx]
    have h1 := hv x hx
    have h2 := cf.isEta.unr v x hx
    change (tp.tup (X.nd.mu i) j).loc v x * (cf.eta.loc v x)⁻¹ = 1 at h1
    rw [h2, inv_one, mul_one] at h1
    exact h1
  have hval : ∀ v, ((X.nd.l i : ℕ) : 𝓞 D.host.E) ∉ v.asIdeal → (tp.tup (X.nd.mu i) j * cf.eta⁻¹).UnrAt v →
      ∀ (A' : ValuationSubring X.nd.Om) (τ : G D.host.E X.nd.Om), IsPlaceOver A' v → IsFrob (F := D.host.E) A' (normV v) τ →
      ι ((r τ : (Qbar (X.nd.l i))ˣ) : Qbar (X.nd.l i)) =
        (((tp.tup (X.nd.mu i) j * cf.eta⁻¹).val v)⁻¹ : ℂˣ).1 *
          ((normV v : ℕ) : ℂ) ^ (((((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) : ℝ) : ℂ) := by
    intro v hl hu A' τ hA' hτ
    rw [hLr.frob_unr ha (Or.inl hl) (hub v hu) hA' hτ, map_inv₀, ι.apply_symm_apply, GlobalTheory.GalChar.block_val,
      mul_inv, ← Complex.cpow_neg, ← Units.val_inv_eq_inv_val, GlobalTheory.ChiLocGal.normV_eq_absNorm]
    congr 2
    unfold Ranks.nV
    push_cast
    ring
  have hev : ∀ᶠ P in Filter.cofinite, P ∉ Bf := Filter.eventually_cofinite.2 (by simpa using Bf.finite_toSet)
  have heq : GlobalTheory.GalChar.inQ (Sp.iq i) (X.nd.chi i 1) = r := by
    refine GlobalTheory.GalChar.eq_of_frob ha hρ hr ?_
    filter_upwards [hev, GlobalTheory.GalChar.away_ae (E := D.host.E) (X.nd.l i) hlne] with v hv hl A' hA' σ' hσ'
    refine GlobalTheory.ChiLocGal.frob_any (X.nd.plOm.2 v) hA' (fun τ hτ => ?_) hσ'
    obtain ⟨hu, hv2⟩ := hBf v hv
    apply Units.ext
    apply ι.injective
    rw [hval v hl hu _ τ (X.nd.plOm.2 v) hτ, ← hv2 τ hτ]
    rfl
  have hwl : ((X.nd.l i : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := hw.2.1
  have hwu : (tp.tup (X.nd.mu i) j * cf.eta⁻¹).UnrAt w := by
    obtain ⟨-, hwl', hwS, hwQ⟩ := hw
    have hS := X.nd.S_def i w
    have hnS : ¬ (w ∈ placesOver D.host.E (D.host.g 0) ∨ w ∈ placesOver D.host.E (D.host.g 1) ∨
        w ∈ placesOver D.host.E (if X.nd.l i = D.host.pde then D.host.pde' else D.host.pde)) :=
      fun h => hwS (hS.2 ⟨h, hwl'⟩)
    push Not at hnS
    obtain ⟨hg0, hg1, hd⟩ := hnS
    have hmu : (cf.mu0 j).UnrAt w := (cf.isMu0 j).unr w (fun k => by
      fin_cases k
      · exact hg0
      · exact hg1)
    have hxi : tp.xi (X.nd.mu i) = cf.delAt (X.nd.l i) * tp.psi (X.nd.w i) := by
      rw [X.nd.mu_w i, tp.xi_tw, X.nd.w_l i]
    have hdel : (cf.delAt (X.nd.l i)).UnrAt w := by
      unfold CharFrame.delAt
      split_ifs with h
      · rw [if_pos h] at hd
        exact cf.isDel'.unr w hd
      · rw [if_neg h] at hd
        exact cf.isDel.unr w hd
    have hmem : i ∈ X.nd.locs (X.nd.j i) (X.nd.w i) := (X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
    have hQ : X.nd.Q i = C.Q (X.nd.w i) := (Sp.Q_eq _ _ i hmem).trans (Sp.Qc_eq _ _)
    have hpsi : (tp.psi (X.nd.w i)).UnrAt w := by
      have := tp.psi_is (X.nd.w i) (X.nd.w_tw i)
      rw [X.nd.w_l i] at this
      exact (this.ram w).2 (hQ ▸ hwQ)
    unfold TupTied.tup
    rw [hxi]
    exact (hmu.mul (hdel.mul hpsi)).mul (cf.isEta.unr w).inv
  rw [← hval w hwl hwu B σ hB hσ, ← heq]
  rfl
end GlobalTheory.ChiMuArtin
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ChiOneRead
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.ChiOneRead
theorem chiOne_read_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (hψ : ∀ w, D.what₂.muAt w ≠ D.what₂.mu0 → (tp.psi w).ValuesIn 0 D.what₂.embLL) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (j : Fin D.R.m), j.1 + 1 = X.nd.j i → ∃ Bf : Finset (HeightOneSpectrum (𝓞 D.host.E)), ∀ P ∉ Bf, (tp.tup (X.nd.mu i) j * cf.eta⁻¹).UnrAt P ∧ ∀ σ : Formalism.ConjugateSelfDual.G D.host.E X.nd.Om, IsFrob (F := D.host.E) (X.nd.plOm.1 P) (normV P) σ → (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)) ((X.nd.chi i 1 σ : (X.nd.O i)ˣ) : X.nd.O i))) = (((tp.tup (X.nd.mu i) j * cf.eta⁻¹).val P)⁻¹ : ℂˣ).1 * ((normV P : ℕ) : ℂ) ^ (((((D.R.t : ℝ) - 1) / 2 + (1 - (D.R.nV : ℝ)) / 2) : ℝ) : ℂ) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh hψ big X T Sp i j hj
  classical
  obtain ⟨B1, h1⟩ := Bs.chi.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) (X.nd.j_range i).1 (X.nd.j_range i).2
  have hpsi := tp.psi_is (X.nd.w i) (X.nd.w_tw i)
  have hfin := Formalism.L2.NC.finite_placesOver (E := D.host.E) (X.nd.l i)
  refine ⟨B1 ∪ C.Q (X.nd.w i) ∪ hfin.toFinset, fun P hP => ?_⟩
  have hP1 : P ∉ B1 := fun h => hP (Finset.mem_union_left _ (Finset.mem_union_left _ h))
  have hPQ : P ∉ C.Q (X.nd.w i) := fun h => hP (Finset.mem_union_left _ (Finset.mem_union_right _ h))
  have hPl : P ∉ placesOver D.host.E (X.nd.l i) := fun h => hP (Finset.mem_union_right _ (hfin.mem_toFinset.2 h))
  obtain ⟨α, hα, x, hx, hσ⟩ := h1 P hP1
  have hxi : tp.xi (X.nd.mu i) = cf.delAt (X.nd.l i) * tp.psi (X.nd.w i) := by
    rw [X.nd.mu_w i, tp.xi_tw, X.nd.w_l i]
  have hl' : D.ntw.l (T.twOf i) = X.nd.l i := T.twOf_l i
  have key : ∀ z : (AdeleRing (𝓞 D.host.E) D.host.E)ˣ, (Bs.chiD.firstHeckeCharacter (T.twOf i) (X.nd.j i)).χ z =
      (cf.mu0 j).1 z * (cf.delAt (X.nd.l i)).1 z * (cf.eta.1 z)⁻¹ := by
    intro z
    change (Bs.chiD.mu0 (X.nd.j i)).χ z * (Bs.chiD.del (T.twOf i)).χ z * ((Bs.chiD.etaT).χ z)⁻¹ = _
    rw [← hj, Bs.ringSpec_normalisedCharacter_eq j z, Bs.eta_eq]
    have hd := Bs.del_eq (T.twOf i) z
    rw [hl'] at hd
    erw [hd]
  have hloc : ∀ (χ : HChar D.host.E) (u : (P.adicCompletion D.host.E)ˣ),
      χ.loc P u = χ.1 (Units.map (Formalism.L2.NC.locM P) u) := fun χ u => by
    rw [← localIdele_eq]; rfl
  have hunr : (tp.tup (X.nd.mu i) j * cf.eta⁻¹).UnrAt P := by
    intro u hu
    have e1 := hα.1 u hu
    rw [key] at e1
    have e2 : (tp.psi (X.nd.w i)).loc P u = 1 := ((hpsi.ram P).2 hPQ) u hu
    rw [hloc] at e2
    rw [hloc]
    show (cf.mu0 j * tp.xi (X.nd.mu i) * cf.eta⁻¹).1 _ = 1
    rw [hxi]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, MonoidHom.mul_apply, MonoidHom.inv_apply] at e1 e2 ⊢
    rw [e2, mul_one]
    exact e1
  refine ⟨hunr, fun σ hσF => ?_⟩
  have hϖ : IsUnifAt P (atFin P (unif P)) := unif_spec P
  have hαv : α = ((cf.mu0 j).val P : ℂ) * ((cf.delAt (X.nd.l i)).val P : ℂ) * ((cf.eta.val P : ℂˣ) : ℂ)⁻¹ := by
    rw [← hα.2 _ hϖ, key]
    simp only [HChar.val, HChar.locK, HChar.loc, MonoidHom.comp_apply, localIdele_eq, Units.val_mul,
      Units.val_inv_eq_inv_val]
  have hc : ((X.nd.chi i 1 σ : (X.nd.O i)ˣ) : X.nd.O i) =
      T.twist₂ i (((lay0 D).ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) σ : ((lay0 D).ntw.O0 (T.twOf i))ˣ) : (lay0 D).ntw.O0 (T.twOf i)) *
        (T.psiL i σ : X.nd.O i) := by
    rw [T.chi_tw i]; rfl
  have hR1 : (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i))
      (T.twist₂ i (((lay0 D).ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) σ : ((lay0 D).ntw.O0 (T.twOf i))ˣ) : (lay0 D).ntw.O0 (T.twOf i))))) =
      D.what₂.embLL (x : D.what₂.LL) := by
    have e := T.twO_emb i x (((lay0 D).ntw.chi1 (T.twOf i) (X.nd.j i) (T.twSide i) σ : ((lay0 D).ntw.O0 (T.twOf i))ˣ) : (lay0 D).ntw.O0 (T.twOf i)) (hσ σ hσF)
    rw [← e, Sp.iq_LL]
  obtain ⟨ψ0, -, h2, -⟩ := hCS.nct.psi_eq
  have hR2 : (qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))) (Sp.iq i (algebraMap (X.nd.O i) (FractionRing (X.nd.O i))
      (T.psiL i σ : X.nd.O i))) = D.what₂.embLL ((ψ0 (X.nd.w i) σ : (D.what₂.LL)ˣ) : D.what₂.LL) := by
    have e3 := Sp.psi_eq i σ _ (h2 (X.nd.w i) σ)
    rw [← e3, Sp.iq_LL]
  obtain ⟨y, hy⟩ := hψ (X.nd.w i) (X.nd.w_tw i) P ((hpsi.ram P).2 hPQ)
  have hy' : D.what₂.embLL y⁻¹ = ((((tp.psi (X.nd.w i)).val P)⁻¹ : ℂˣ) : ℂ) := by
    rw [map_inv₀, hy]
    simp [HChar.valTw]
  have hl2 : P ∉ placesOver D.host.E (D.what₂.places.resChar (X.nd.w i)) := by rw [X.nd.w_l i]; exact hPl
  have e4 := hCS.psi (X.nd.w i) (X.nd.w_tw i) P hPQ hl2 (X.nd.plOm.1 P) σ (X.nd.plOm.2 P) hσF y⁻¹ hy'
  have e5 : ((ψ0 (X.nd.w i) σ : (D.what₂.LL)ˣ) : D.what₂.LL) = y⁻¹ :=
    (C.embW (X.nd.w i)).injective (by rw [e4]; exact h2 _ σ)
  rw [hc, map_mul, map_mul, map_mul, hR1, hR2, e5, hy']
  have hx' : D.what₂.embLL (x : D.what₂.LL) = α⁻¹ * ((Real.sqrt (normV P) : ℝ) : ℂ) ^ (-(D.R.r : ℤ)) := hx
  rw [hx', ← sqrt_zpow (normV P) D.R.r D.R.t D.R.nV rfl, hαv]
  simp only [TupTied.tup, hxi, HChar.val_mul, HChar.val_inv, Units.val_mul, Units.val_inv_eq_inv_val]
  ring
end GlobalTheory.ChiOneRead
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsIsRc
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain
namespace GlobalTheory.TypeRec.Model
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField GlobalTheory.TypeRec.factG
section Compl
variable {F : Type} [Field F] [NumberField F] (w : HeightOneSpectrum (𝓞 F)) (p : ℕ) [hp : Fact p.Prime]
end Compl
open Classical in
theorem exists_isRc_alt (hL : _root_.UpperTheory.Zero.LLC.RecTExists) {D : D7} (T : GlobalTheory.RowTie.WDTie D.nd D.naut) (I : Ident D) :
    ∃ rc, _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc := by
  refine ⟨fun k v n π => if h : ∃ σ, Nonempty (π ≅ pull I k v σ) then
    (T.e _).symm (_root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 (D.naut.plGw k v)) (GlobalTheory.LocLanglands.cls h.choose))
    else D.naut.lpZero _, fun k v n σ π h => ?_⟩
  have h' : ∃ σ, Nonempty (π ≅ pull I k v σ) := ⟨σ, h⟩
  beta_reduce
  rw [dite_eq_left h', Equiv.apply_symm_apply, cls_eq_of_iso I k v _ σ ⟨h'.choose_spec.some.symm ≪≫ h.some⟩]
theorem locR_eq_rc_of_isRc_and_true_reading {hL : _root_.UpperTheory.Zero.LLC.RecTExists} {D : D7} {T : GlobalTheory.RowTie.WDTie D.nd D.naut} {I : Ident D} {rc}
    (h : _root_.GlobalTheory.TypeRec.IsSeriesCorrespondence hL T I rc) {rep cp} (hc : IsComp I rep cp) {loc : D.what₂.FT → ∀ w, D.naut.LP w} {sat}
    (hr : _root_.GlobalTheory.HeightCounting.RepresentationParametersHold hL D rep (fun σ w => T.e w (loc σ w)) sat) (σ k v) :
    loc σ (D.naut.plGw k v) = rc k v D.R.r (cp σ k v) := by
  obtain ⟨s, hs, τ, h1, h2⟩ := hc σ k v
  apply (T.e _).injective
  rw [h2, h k v _ τ _ ⟨CategoryTheory.Iso.refl _⟩]
  have key : ∀ (w) (hs : s.w = w) (τ : GlobalTheory.SmGL.IrrRep (GL (Fin D.R.r) (w.adicCompletion D.host.E))),
      GlobalTheory.HeightCounting.IsLocS (rep σ).S s (hs ▸ τ) → T.e w (loc σ w) =
        _root_.GlobalTheory.CuspRep.ParLawsT.locRecT hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls τ) := by
    rintro _ rfl τ h1
    exact hr.1 σ s τ h1
  exact key _ hs τ h1
end GlobalTheory.TypeRec.Model
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsIsRepOfTw
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
noncomputable section
namespace GlobalTheory.HeightCounting.TwistAny
open Formalism.L2.NR
theorem exists_isRepOf_tw_alt : GlobalTheory.Published.GlobalArtinReciprocity → ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE), GalEx D → ∀ (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (π : D.naut.CG D.R.r), D.naut.csd π → D.naut.ralg π → ∃ ρ : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin D.R.r) (Qbar l), IsRepOf D l ι (D.naut.tw π D.naut.etaTinv) ((1 - (D.R.nV : ℝ)) / 2) ρ := by
  intro hGA D cf jE A hGal l _ ι π hc hr
  obtain ⟨ρ₁, c1, ss1, f1⟩ := hGal l ι D.R.r (Formalism.L2.NR.one_le_r D) π hc hr
  obtain ⟨n, hn⟩ := (GlobalTheory.Mem.CharAlg.isAlg_even_odd D.R D.host).2 cf.eta cf.isEta.inf D.R.t D.R.t_odd
  obtain ⟨art, ha⟩ := hGA D.host.E D.nd.Om
  obtain ⟨μ, hμc, hμ⟩ := ha.exists_isLAdicOf ι (GlobalTheory.HeckeGal.isAlgPos_of_isAlg hn)
  refine ⟨Formalism.MainNotions.SumRepresentations.At.twGL ρ₁ μ, ?_, GlobalTheory.TwistLG.isSSRep_twGL _ _ ss1, ?_⟩
  · simp only [GlobalTheory.TwistLG.twGL_val]
    exact (Units.continuous_val.comp hμc).smul c1
  have hfin := placesOver_finite D.host.E l (Fact.out : l.Prime).ne_zero
  filter_upwards [f1, D.naut.locG_unr_ae π, hfin.compl_mem_cofinite] with w hw1 hu hwl
  intro B σ hB hσ
  have hwl' : ((l : ℕ) : 𝓞 D.host.E) ∉ w.asIdeal := hwl
  have hue : D.naut.unr (D.naut.locG D.naut.etaTinv w) := (D.naut.etaTinv_def w).1
  have hU := (A.chr.unr_iff _ w).1 hue
  have hf := A.chr.frob _ w hU
  rw [A.chr.etaTinv] at hf hU
  have hν := GlobalTheory.HeckeGal.Model.absPow_isAbsPow D.host.E (-(D.R.t : ℝ) / 2)
  have hψu : (cf.eta⁻¹ * GlobalTheory.HeckeGal.Model.absPow D.host.E (-(D.R.t : ℝ) / 2)).UnrAt w := by
    intro x hx
    change (cf.eta⁻¹).loc w x * (GlobalTheory.HeckeGal.Model.absPow D.host.E (-(D.R.t : ℝ) / 2)).loc w x = 1
    rw [hU x hx, hν.1 w x hx, one_mul]
  have hμv := hμ.frob_unr ha (Or.inl hwl') hψu hB hσ
  set u : ℂ := (((cf.eta⁻¹ * GlobalTheory.HeckeGal.Model.absPow D.host.E (-(D.R.t : ℝ) / 2)).val w : ℂˣ) : ℂ)⁻¹ with hu_def
  have hu1 : D.naut.frobEig (D.naut.lpTw (D.naut.locG D.naut.etaTinv w) (-(D.R.t : ℝ) / 2)) = {u} := by
    rw [D.naut.frobEig_tw _ _ hue, hf, Multiset.map_singleton]
    congr 1
    rw [hu_def, HChar.val_mul, HChar.val_inv, Units.val_mul, hν.2.1 w]
    have hn' : (Ideal.absNorm w.asIdeal : ℕ) = normV w := by
      simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]
    rw [hn', mul_inv, Units.val_inv_eq_inv_val, Complex.cpow_neg, inv_inv]
  have hχu : ι ((μ σ : (Qbar l)ˣ) : Qbar l) = u := by
    rw [hμv, map_inv₀, ι.apply_symm_apply]
  have h1 := hw1 B σ hB hσ
  rw [GlobalTheory.TwistLG.twGL_val, ← Matrix.charpoly_map, GlobalTheory.ParamRep.map_smul_matrix,
    GlobalTheory.ParamRep.galPol_twist D.nd D.naut π hu u hu1]
  have h2 : ((((ρ₁ σ : GL _ _) : Matrix (Fin D.R.r) (Fin D.R.r) _).map ι.toRingHom)).charpoly =
      ((D.naut.frobEig (D.naut.lpTw (D.naut.locG π w) ((1 - (D.R.r : ℝ)) / 2))).map fun α => X - C α).prod := by
    rw [Matrix.charpoly_map]; exact h1
  have h3 := GlobalTheory.ParamRep.charpoly_smul_of_prod _ u _ h2
  have hχu' : ι.toRingHom ((μ σ : (Qbar l)ˣ) : Qbar l) = u := hχu
  rw [hχu']
  exact h3
end GlobalTheory.HeightCounting.TwistAny
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsMuC
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.MuCLoc
theorem exists_muC_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc), ∃ μ : D.naut.CG 1, D.naut.csd μ ∧ ∀ j : Fin D.R.m, j.1 + 1 = X.nd.j i → (A.chr.e1 μ).1 = tp.tup (X.nd.mu i) j := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i
  obtain ⟨h1, h2⟩ := X.nd.j_range i
  let j : Fin D.R.m := ⟨X.nd.j i - 1, by omega⟩
  refine ⟨A.chr.e1.symm ⟨tp.tup (X.nd.mu i) j, tp.tup_unitary (X.nd.mu i) j⟩, ?_, ?_⟩
  · rw [A.chr.csd, Equiv.apply_symm_apply]
    exact GlobalTheory.CsdTriv.isCSD_of_trivOn _ _ _ ((cf.isMu0 j).triv.mul (tp.xi_triv (X.nd.mu i)))
  · intro j' hj'
    have : j' = j := Fin.ext (by simp only [j]; omega)
    subst this
    rw [Equiv.apply_symm_apply]
end GlobalTheory.MuCLoc
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ExistsResidueFieldMap
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.ResidueLocPlace
end GlobalTheory.ResidueLocPlace
namespace GlobalTheory.ResidueLocPlace
end GlobalTheory.ResidueLocPlace
theorem GlobalTheory.ResidueLocPlace.exists_residueField_map_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (low : Finset ℕ) (Pq : HeightOneSpectrum (𝓞 (maximalRealSubfield D.host.E)) → PlE D.host) (S : RatDat D.ntw) (hL : ∀ j, ℕ → PlE D.host → Module.End D.what₂.LL (S.WL j)) (eig : ℕ → D.what₂.FT → ℕ → PlE D.host → ↥D.LL0) (θ : ∀ kk : Fin 2, Multiplicative (ZMod (D.host.g kk)) →* (↥D.LL0)ˣ) (Bs : SideB D cf A.row low Pq S hL eig θ) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hCS : ChoiceSide D cf M Bs.exp C tp) (hMI : MtInput D M tp.tup C.Q) (hstar : ∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) (hE : ∀ j g, ∃ z : ℤ, eExp D j g = z) (hsp : ∀ v, v ∈ placesOver D.host.E D.host.pde ∨ v ∈ placesOver D.host.E D.host.pde' → IsSplitPl D.host v) (hCh : GlobalTheory.RowTie.ChebSplit D.nd) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc), ∃ κ : IsLocalRing.ResidueField (X.nd.O i) →+* Formalism.CyclotomicNorms.Fbar (X.nd.l i), ∀ y : X.nd.O i, ∃ h : (((qCast (X.nd.w_l i) (A.pl.ι (X.nd.w i))).toRingHom.comp (Sp.iq i)).comp (algebraMap (X.nd.O i) (FractionRing (X.nd.O i)))) y ∈ A.pl.plB (X.nd.w i), fbCast (X.nd.w_l i) (D.what₂.places.resChar_prime (X.nd.w i)) (X.nd.lPrime i).out (A.pl.plκ (X.nd.w i) (IsLocalRing.residue (A.pl.plB (X.nd.w i)) ⟨_, h⟩)) = κ (IsLocalRing.residue (X.nd.O i) y) := by
  intro D cf jE A low Pq S hL eig θ Bs M C tp hCS hMI hstar hE hsp hCh big X T Sp i
  exact GlobalTheory.ResidueLocPlace.exists_residue_lift (X.nd.w_l i) _ _ (A.pl.ι (X.nd.w i)) (A.pl.plB (X.nd.w i))
    (A.pl.plB_eq (X.nd.w i)) (A.pl.plκ (X.nd.w i)) (Sp.iq i) (Sp.iq_alg i)
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ForcedByAutomorphicSemisimpleData
section
set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host GlobalTheory.HeightCounting NumberField IsDedekindDomain
namespace GlobalTheory.CoefDuty
variable {D : D7} {cf : CharFrame D} {jE : D.host.E →+* Qb}
def BuiltAlt (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E)
    (big : D.what₂.places.Pl → Finset ℂ) (L : LocAll (lay0 D)) : Prop :=
  ∃ Sp : NdSpec A.pl M C big L.X L.T, Nonempty (_root_.GlobalTheory.HeightCounting.AutomorphicSpecialisation A M tup Sp.iq L.Y L.C) ∧ ∀ σ lam, IsSSRep (L.Z.rbar σ lam)
def AutomorphicSideExists (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E) : Prop :=
  ∀ big, ∃ L, _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L
def ForcedByAutomorphicSemisimpleData (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tup : D.what₂.Tup → Fin D.R.m → HChar D.host.E)
    (P : D7 → Prop) : Prop :=
  ∃ big, ∀ L, _root_.GlobalTheory.CoefDuty.BuiltAlt A M C tup big L → P (withLoc L)
end GlobalTheory.CoefDuty
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.GoodPartLeISupEigen
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct
noncomputable section
namespace GlobalTheory.HeightCounting.FormsStep
theorem goodPart_le_iSup_eigen_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (S : RatDat D.ntw)
    (In : RatIn D S) (b0 b1 : Big D) (Sx : Finset (PlE D.host)) (T : TwR D.LL0 D.nd) (Sp : RingSpec D cf b0 b1 Sx T),
    In.Sb ⊆ Sx → (∀ x : D.LL0, star (x : D.what₂.LL) ∈ D.LL0) →
    ∀ (i : T.Tw) (j : ℕ) (b : Bool), 1 ≤ j → j ≤ D.R.m →
      V0T D T S In.rho In.chi In.θ i j b ≤
        ⨆ σ ∈ {σ : D.what₂.FT | D.what₂.isot j σ ≠ ⊥ ∧ D.nd.goodRow σ},
          V0T D T S In.rho In.chi In.θ i j b ⊓
            ⨅ (k : ℕ) (P : PlE D.host) (_ : 1 ≤ k ∧ k ≤ D.R.r ∧ IsSplitPl D.host P ∧ P ∉ T.S0 i),
              Module.End.eigenspace (hkT D T S In i j b k P)
                (algebraMap (T.O i) (FractionRing (T.O i)) (cHkT D T i b P : T.O i) ^ k * readT D T i b (In.eig j σ k P)) := by
  intro D cf jE A S In b0 b1 Sx T Sp hSb hstar i j b hj1 hj2
  obtain ⟨Φ, hc, hf, hw⟩ := descend_exists D T S In i j b hj1 hj2
  have ha := descend_actL D T S In i j b hj1 hj2 Φ hc hf
  have he := descend_eSum D T S In i j b Φ hc ha
  refine (_root_.GlobalTheory.HeightCounting.FormsStep.goodTwistSideForms_le_span_goodLiftForms D S In T i j b hj1 hj2 (eIdem_all D) Φ hc ha he hw).trans (Submodule.span_le.mpr ?_)
  intro y hy
  obtain ⟨x, hx, rfl⟩ := hy
  rw [SetLike.mem_coe]
  refine Submodule.iSup_induction (motive := fun y => Φ y ∈ _) _ (In.span j hj1 hj2 hx) ?_ ?_ ?_
  · intro σ y hy
    refine Submodule.iSup_induction (motive := fun y => Φ y ∈ _) _ hy ?_ ?_ ?_
    · intro hσ z hz
      refine Submodule.mem_iSup_of_mem σ (Submodule.mem_iSup_of_mem hσ ?_)
      rw [Submodule.mem_inf] at hz ⊢
      refine ⟨descend_mem_V0T D T S In i j b Φ hc ha he z hz.1, ?_⟩
      have hz2 := hz.2
      simp only [Submodule.mem_iInf] at hz2 ⊢
      intro k P hkP
      have hPb : P ∉ In.Sb := fun hP => hkP.2.2.2 (by
        rw [← Finset.mem_coe, Sp.ringSpec_excludedPlaces_eq i]
        exact Or.inr (Finset.mem_coe.mpr (hSb hP)))
      exact descend_mem_eigenspace D T S In i j b hj1 hj2 Φ hc hf k P _ z (hz2 k P ⟨hkP.1, hkP.2.1, hkP.2.2.1, hPb⟩)
    · rw [map_zero]; exact zero_mem _
    · intro y z hy hz; rw [map_add]; exact add_mem hy hz
  · rw [map_zero]; exact zero_mem _
  · intro y z hy hz; rw [map_add]; exact add_mem hy hz
end GlobalTheory.HeightCounting.FormsStep
end
end
end

-- bundled from Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.LevelAtSplitOut
section
set_option synthInstance.maxHeartbeats 200000

section
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting NumberField IsDedekindDomain Polynomial
namespace GlobalTheory.LocLevel
set_option maxHeartbeats 4000000 in
set_option synthInstance.maxHeartbeats 400000 in
theorem level_at_splitOut_alt : ∀ (D : D7) (cf : CharFrame D) (jE : D.host.E →+* Qb) (A : _root_.GlobalTheory.HeightCounting.CharFrameHostEmbedding D cf jE) (M : MtFam D) (C : NChoice D) (tp : TupTied D cf C) (hMI : MtInput D M tp.tup C.Q) (big : D.what₂.places.Pl → Finset ℂ) (X : LocNd (lay0 D)) (T : LocTw X) (Sp : NdSpec A.pl M C big X T) (i : X.nd.Loc) (w : PlE D.host) (s : SplitPlace D.host.E), SplitOut X.nd i w → IsConjPl D.host w s.w → ∀ κ : GAf D.host.E D.R.nV, TrivOutside {s.v} κ → (κ ∈ (mlX M X i).J ↔ κ ∈ Umax D.host.E D.R.nV) ∧ ∀ h : κ ∈ (mlX M X i).J, (mlX M X i).χ ⟨κ, h⟩ = 1 := by
  intro D cf jE A M C tp hMI big X T Sp i w s hw hc κ htr
  classical
  have hov : NG.OverPl w s.v := overPl_of_isConjPl hc
  have hjf : X.nd.j i - 1 + 1 = X.nd.j i := by have := X.nd.j_range i; omega
  let jf : Fin D.R.m := ⟨X.nd.j i - 1, by have := X.nd.j_range i; omega⟩
  have h0 := hMI.hyp (X.nd.w i) jf
  have hyp : NG.HypOutside (mlX M X i).J (mlX M X i).χ (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf)) :=
    GlobalTheory.FitHecke.hypOutside_transport' (M := M) (X.nd.mu_w i).symm hjf _ _ (X.nd.j_range i).1 (X.nd.j_range i).2 _ h0
  have hS := (X.nd.S_def i w).not.1 hw.2.2.1
  have hl := hw.2.1
  have hg : ∀ k, w ∉ placesOver D.host.E (D.host.g k) := by
    intro k hk
    apply hS
    refine ⟨?_, hl⟩
    fin_cases k
    · exact Or.inl hk
    · exact Or.inr (Or.inl hk)
  have hp : w ∉ placesOver D.host.E (if X.nd.l i = D.host.pde then D.host.pde' else D.host.pde) :=
    fun h => hS ⟨Or.inr (Or.inr h), hl⟩
  have hi : i ∈ X.nd.locs (X.nd.j i) (X.nd.w i) := (X.nd.locs_mem _ _ i).2 ⟨rfl, rfl⟩
  have hQe : C.Q (X.nd.w i) = Sp.B.Qc (X.nd.j i) (X.nd.w i) := (Sp.Qc_eq _ _).symm
  have hvB : s.v ∉ gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf) := by
    rintro (⟨w', hov', k, hk⟩ | hq)
    · exact hg k (mem_placesOver_of_overPl' hov hov' hk)
    · obtain ⟨w', hov', hw'⟩ := GlobalTheory.FitHecke.qPl_sub tp (X.nd.w i) (X.nd.w_tw i) jf hq
      rcases hw' with hQ' | hp'
      · rw [hQe] at hQ'
        have hwQ : w ∈ Sp.B.Qc (X.nd.j i) (X.nd.w i) := Sp.B.Qc_over _ _ w' w hQ' ⟨s.v, hov', hov⟩
        rw [← Sp.Q_eq _ _ i hi] at hwQ
        exact hw.2.2.2 hwQ
      · rw [X.nd.w_l i] at hp'
        exact hp (mem_placesOver_of_overPl' hov hov' hp')
  have htr' : TrivOutside (gPl D ∪ qPl D (tp.tup (D.what₂.muTw (X.nd.w i)) jf))ᶜ κ := by
    intro v hv
    apply htr v
    rintro rfl
    exact hv hvB
  exact hyp κ htr'
end GlobalTheory.LocLevel
end
end

