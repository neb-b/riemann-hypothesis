module

public import Development.AutomorphicArithmetic.Foundations.Convolution.LocalGroupAnalysis.Bundle0005
public import GroundTheory.AutomorphicForms.Bundle0010

@[expose] public section

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.InfinitePartFiniteOfAdelicBound
section
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

private theorem mapGL_id' {R : Type} [CommRing R] (n : ℕ) (x : Matrix.GeneralLinearGroup (Fin n) R) :
    PositivityTheory.Rg.Tf.Geo.mapGL n (RingHom.id R) x = x := by
  ext i j
  simp

theorem UpperTheory.infinitePart_finite_of_adelicBound :
    P2 → Triv → BoundE → InfF := by
  intro hP hT hB F _ _ n hn γ
  have hz : ∀ τ : F ≃ₐ[F] F, τ ∈ Subgroup.zpowers (1 : F ≃ₐ[F] F) := fun τ => by
    have h1 : τ = 1 := by
      ext x
      exact τ.commutes x
    rw [h1]
    exact one_mem _
  obtain ⟨hg, hi, -⟩ := hT F
  have hi' : GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (K := F) (L := F) = RingHom.id _ := hi
  have hB' := hB F F 1 hz n hn γ
  have hP' := (hP F F 1 hz n hn).2 γ γ
  rw [hg] at hB' hP'
  rw [hi'] at hP'
  simp only [mapGL_id'] at hB' hP'
  refine ⟨hB', fun hs D hD => ?_⟩
  have hN : PositivityTheory.Rg.Tf.Loc.twNorm (mapGL n (RingHom.id _)) (Module.finrank F F) γ = γ := by
    simp [PositivityTheory.Rg.Tf.Loc.twNorm]
    rfl
  obtain ⟨C, hC, h⟩ := hP' hs hN D hD
  exact ⟨C, hC, h⟩
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.MaximalCompactNormOfUnitCriterion
section
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal

theorem UpperTheory.maximalCompactNorm_of_unit_criterion :
    K1 → Triv → UnitIff → Compat → SelmerRankBoundLaurent := by
  intro hK hT hU hC F _ _ n hn γ hγ
  have hincl : PositivityTheory.Rg.Tf.Loc.incl γ = γ := by
    ext i j
    rfl
  have hnorm : PositivityTheory.Rg.Tf.Loc.normGL (1 : F ≃ₐ[F] F) γ = PositivityTheory.Rg.Tf.Loc.incl γ := by
    rw [hincl, PositivityTheory.Rg.Tf.Loc.normGL, Module.finrank_self]
    simp [PositivityTheory.Rg.Tf.Loc.twNorm]
  have h1 : ∀ τ : F ≃ₐ[F] F, τ ∈ Subgroup.zpowers (1 : F ≃ₐ[F] F) := fun τ => by
    have : τ = 1 := AlgEquiv.ext fun x => τ.commutes x
    rw [this]
    exact one_mem _
  obtain ⟨-, -, -, c4, -, -, -, c8⟩ := hC F F 1 n
  filter_upwards [hK F F 1 h1 n hn γ γ hγ hnorm] with v hv x
  have hdiag : mapGL n (atFin v) (AdelicGLn.diagonal F n γ) =
      mapGL n (incFin F v) (finAt v (AdelicGLn.diagonal F n γ)) := by
    have h := c4 v (AdelicGLn.diagonal F n γ)
    rw [c8, hincl] at h
    exact h
  have hgal : ∀ y : GL (Fin n) (CompletionsOver F v), mapGL n (galFin (1 : F ≃ₐ[F] F) v) y = y := fun y => by
    rw [((hT F).2.2 v).1]
    ext i j
    rfl
  have key := hv (mapGL n (incFin F v) x)
  rw [hdiag, hgal, ← map_inv, ← map_mul, ← map_mul, hU F F n v] at key
  rw [key]
  constructor
  · rintro ⟨t, ht, y, hy, e⟩
    refine ⟨t, ht, t⁻¹ * x, ?_, by group⟩
    rw [← hU F F n v, map_mul, map_inv, e, inv_mul_cancel_left]
    exact hy
  · rintro ⟨t, ht, y, hy, rfl⟩
    exact ⟨t, ht, mapGL n (incFin F v) y, (hU F F n v y).2 hy, map_mul _ _ _⟩
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.OrbitalSideBaseFieldOfAbsoluteConvergence
section
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

open MeasureTheory NumberField IsDedekindDomain Topology Filter GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
theorem UpperTheory.orbitalSideBaseField_of_absoluteConvergence :
    SideAbs → RPF → RPCen → UniLoc → UniOf → TComm → SepLoc → CentLoc → InfF → SideF := by
  intro hS hRP hRC hUL hUO hTC hSep hCL hInf F _ _ n hn _ _ _ _ μ μi m hμ hμi hm γ hγ ν νi nv hν hνi hnv S a b ha hb hT hE
    fi f hfi hfc hf hloc
  have hcA : IsClosed ((TA γ : Subgroup (GA F n)) : Set (GA F n)) := Set.isClosed_centralizer _
  have hcI : IsClosed ((TI γ : Subgroup (GL (Fin n) (InfiniteAdeleRing F))) : Set (GL (Fin n) (InfiniteAdeleRing F))) :=
    Set.isClosed_centralizer _
  have hcF : ∀ v : Pl F, IsClosed ((TF γ v : Subgroup (GL (Fin n) (v.adicCompletion F))) :
      Set (GL (Fin n) (v.adicCompletion F))) := fun v => Set.isClosed_centralizer _
  haveI : LocallyCompactSpace (TA γ) := hcA.locallyCompactSpace
  haveI : LocallyCompactSpace (TI γ) := hcI.locallyCompactSpace
  haveI : ∀ v : Pl F, LocallyCompactSpace (TF γ v) := fun v => (hcF v).locallyCompactSpace
  haveI : SecondCountableTopology (TA γ) :=
    TopologicalSpace.Subtype.secondCountableTopology ((TA γ : Subgroup (GA F n)) : Set (GA F n))
  haveI : SecondCountableTopology (TI γ) := TopologicalSpace.Subtype.secondCountableTopology
    ((TI γ : Subgroup (GL (Fin n) (InfiniteAdeleRing F))) : Set (GL (Fin n) (InfiniteAdeleRing F)))
  haveI : ∀ v : Pl F, SecondCountableTopology (TF γ v) := fun v => TopologicalSpace.Subtype.secondCountableTopology
    ((TF γ v : Subgroup (GL (Fin n) (v.adicCompletion F))) : Set (GL (Fin n) (v.adicCompletion F)))
  have hR := hRP F n
  have hRT := hRC _ _ _ _ (pI F n) (pF F n) (KF F n) hR (AdelicGLn.diagonal F n γ)
  obtain ⟨hc1, hc2, hc3, -⟩ := hTC F n γ hγ
  obtain ⟨hUi, hUv⟩ := hUL (Pl F) (GA F n) _ _ (pI F n) (pF F n) (KF F n) hR μ μi m hμ hμi hm
  have hP : Pair μ (TA γ).subtype ν := ⟨hμ, hcA.isClosedEmbedding_subtypeVal, (hUO _ ν hν).2 hc1⟩
  have hPi : Pair μi (TI γ).subtype νi := ⟨hUi, hcI.isClosedEmbedding_subtypeVal, (hUO _ νi hνi).2 hc2⟩
  have hPv : ∀ v : Pl F, Pair (m v) (TF γ v).subtype (nv v) := fun v =>
    ⟨hUv v, (hcF v).isClosedEmbedding_subtypeVal, (hUO _ (nv v) (hnv v)).2 (hc3 v)⟩
  have hz : Continuous (zA F n) :=
    (continuous_centralSection (K := F) (n := n)).comp
      (Continuous.subtype_mk Real.continuous_exp fun s => Real.exp_pos s)
  have hzv : ∀ (v : Pl F) (s : ℝ), pF F n v (zA F n s) = 1 := fun v s => (hCL F n _).2.2.1 v
  have hfix : ∀ t : TA γ, ((TA γ).subtype t)⁻¹ * AdelicGLn.diagonal F n γ * (MonoidHom.id (GA F n)) ((TA γ).subtype t) =
      AdelicGLn.diagonal F n γ := by
    intro t
    have h := Subgroup.mem_centralizer_singleton_iff.1 t.2
    simp only [Subgroup.subtype_apply, MonoidHom.id_apply]
    first
      | rw [mul_assoc, ← h, inv_mul_cancel_left]
      | rw [mul_assoc, h, inv_mul_cancel_left]
  have hcpt : ∀ D : Set (GL (Fin n) (InfiniteAdeleRing F)), IsCompact D → ∃ C : Set (GL (Fin n) (InfiniteAdeleRing F)),
      IsCompact C ∧ ∀ x, x⁻¹ * pI F n (AdelicGLn.diagonal F n γ) * (MonoidHom.id _) x ∈ D →
        ∃ t : TI γ, ∃ y ∈ C, x = (TI γ).subtype t * y := by
    intro D hD
    obtain ⟨C, hC, h⟩ := (hInf F n hn (pI F n (AdelicGLn.diagonal F n γ))).2 (hSep F n γ hγ).1 D hD
    refine ⟨C, hC, fun x hx => ?_⟩
    obtain ⟨t, ht, y, hy, rfl⟩ := h x hx
    exact ⟨⟨t, Subgroup.mem_centralizer_singleton_iff.2 (by first | exact ht | exact ht.symm)⟩, y, hy, rfl⟩
  have hbd : ∀ D : Set (GL (Fin n) (InfiniteAdeleRing F)), IsCompact D → ∃ B : Set ℝ, IsCompact B ∧
      ∀ s x, pI F n (zA F n s) * (x⁻¹ * pI F n (AdelicGLn.diagonal F n γ) * (MonoidHom.id _) x) ∈ D → s ∈ B :=
    (hInf F n hn (pI F n (AdelicGLn.diagonal F n γ))).1
  have hl : ∀ v ∉ S, f v = (KF F n v : Set (GL (Fin n) (v.adicCompletion F))).indicator 1 ∧
      ∀ x, x⁻¹ * pF F n v (AdelicGLn.diagonal F n γ) * (MonoidHom.id _) x ∈ KF F n v ↔
        ∃ t : TF γ v, ∃ y ∈ KF F n v, x = (TF γ v).subtype t * y := by
    intro v hv
    refine ⟨(hloc v hv).1, fun x => ?_⟩
    refine ((hloc v hv).2 x).trans ⟨?_, ?_⟩
    · rintro ⟨t, ht, y, hy, rfl⟩
      exact ⟨⟨t, Subgroup.mem_centralizer_singleton_iff.2 (by first | exact ht | exact ht.symm)⟩, y, hy, rfl⟩
    · rintro ⟨t, y, hy, rfl⟩
      have h := Subgroup.mem_centralizer_singleton_iff.1 t.2
      exact ⟨t, by first | exact h | exact h.symm, y, hy, rfl⟩
  obtain ⟨hm1, hm2⟩ := hS (Pl F) (GA F n) (GL (Fin n) (InfiniteAdeleRing F)) (fun v => GL (Fin n) (v.adicCompletion F))
    (pI F n) (pF F n) (KF F n) (TA γ) (TI γ) (fun v => TF γ v)
    (cen (pI F n) (AdelicGLn.diagonal F n γ)) (fun v => cen (pF F n v) (AdelicGLn.diagonal F n γ))
    (fun v => (KF F n v).comap (TF γ v).subtype) hR hRT (TA γ).subtype (TI γ).subtype (fun v => (TF γ v).subtype)
    (fun _ => rfl) (fun _ _ => rfl) (fun _ _ => Iff.rfl) μ μi m ν νi nv hP hPi hPv S a b ha hb hE hT
    (MonoidHom.id _) (MonoidHom.id _) (fun _ => MonoidHom.id _) (fun _ => rfl) (fun _ _ => rfl)
    continuous_id (fun _ => continuous_id) (AdelicGLn.diagonal F n γ) (zA F n) hz hzv hfix hcpt hbd fi f hfi hfc hf hl
  refine ⟨hm1, ?_⟩
  refine Eq.trans hm2 ?_
  congr 3
  funext s
  congr 1
  funext x
  have hc := (hCL F n ⟨Real.exp s, Real.exp_pos s⟩).2.1
  congr 1
  change pI F n (zA F n s) * (x⁻¹ * pI F n (AdelicGLn.diagonal F n γ) * x) =
    x⁻¹ * (pI F n (zA F n s) * pI F n (AdelicGLn.diagonal F n γ)) * x
  rw [mul_assoc, mul_assoc, ← mul_assoc (pI F n (zA F n s)), hc x⁻¹, mul_assoc, mul_assoc]
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.OrbitalSideExtensionOfAbsoluteConvergence
section
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open MeasureTheory NumberField IsDedekindDomain Topology Filter
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange

private theorem cent_closed {G : Type} [Group G] [TopologicalSpace G] [ContinuousMul G] [T2Space G] (g : G) :
    IsClosed ((Subgroup.centralizer {g} : Subgroup G) : Set G) := by
  have h : ((Subgroup.centralizer {g} : Subgroup G) : Set G) = {x | x * g = g * x} := by
    ext x
    exact Subgroup.mem_centralizer_singleton_iff
  rw [h]
  exact isClosed_eq (continuous_id.mul continuous_const) (continuous_const.mul continuous_id)

theorem UpperTheory.orbitalSideExtension_of_absoluteConvergence :
    SideAbs → RPF → RPE → RPCen → UniLoc → UniOf → TComm → SepLoc → CentLoc → Compat → GalCont → LocEmb → UnitIff → LocNorm → BoundE → N3 → N5 → P2 → SideE := by
  intro hSA hRPF hRPE hRPC hUL hUO hTC hSL hCL hCo hGC hLE hUI hLN hBE hN3 hN5 hP2 F E _ _ _ _ _ _ σ hσ n hn _ _ _ _ _ _ _ _ μ μi m hμ hμi hm γ hγ δ hδ ν νi nv hν hνi hnv S a b ha hb hET hEE
    φi φ hφi hφc hφ hS
  obtain ⟨c1, c2, c3, c4, -⟩ := hCo F E σ n
  obtain ⟨g0, g1, g2⟩ := hGC F E σ n
  obtain ⟨l1, l2⟩ := hLE F E n
  obtain ⟨t1, t2, t3, -⟩ := hTC F n γ hγ
  have hG := hRPE F E n
  have hT := hRPC _ _ _ _ (pI F n) (pF F n) (KF F n) (hRPF F n) (AdelicGLn.diagonal F n γ)
  haveI : LocallyCompactSpace (TA γ) := (cent_closed _).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : LocallyCompactSpace (TI γ) := (cent_closed _).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : ∀ v : Pl F, LocallyCompactSpace (TF γ v) :=
    fun v => (cent_closed _).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology (TA γ) :=
    TopologicalSpace.Subtype.secondCountableTopology ((TA γ : Subgroup (GA F n)) : Set (GA F n))
  haveI : SecondCountableTopology (TI γ) :=
    TopologicalSpace.Subtype.secondCountableTopology ((TI γ : Subgroup _) : Set (GL (Fin n) (InfiniteAdeleRing F)))
  haveI : ∀ v : Pl F, SecondCountableTopology (TF γ v) := fun v =>
    TopologicalSpace.Subtype.secondCountableTopology ((TF γ v : Subgroup _) : Set (GL (Fin n) (v.adicCompletion F)))
  obtain ⟨uI, uV⟩ := hUL (Pl F) (GA E n) _ _ (pI E n) (fun v => pE E n v) (fun v => KE E n v) hG μ μi m hμ hμi hm
  have hZ : Continuous (zA E n) :=
    (continuous_centralSection (K := E) (n := n)).comp (Real.continuous_exp.subtype_mk _)
  have key := hSA (Pl F) (GA E n) (GL (Fin n) (InfiniteAdeleRing E)) (fun v => GL (Fin n) (CompletionsOver E v))
    (pI E n) (fun v => pE E n v) (fun v => KE E n v) (TA γ) (TI γ) (fun v => TF γ v)
    (cen (pI F n) (AdelicGLn.diagonal F n γ)) (fun v => cen (pF F n v) (AdelicGLn.diagonal F n γ))
    (fun v => (KF F n v).comap (TF γ v).subtype) hG hT
    ((mapGL n (adeleMap F E)).comp (TA γ).subtype) ((mapGL n (infMap F E)).comp (TI γ).subtype)
    (fun v => (mapGL n (incFin E v)).comp (TF γ v).subtype)
    (fun t => c3 t.1) (fun v t => c4 v t.1) (fun v t => (hUI F E n v t.1).symm)
    μ μi m ν νi nv
    ⟨hμ, (hN5 F E σ hσ n hn).1.comp (cent_closed _).isClosedEmbedding_subtypeVal, (hUO _ ν hν).2 t1⟩
    ⟨uI, (l1.comp (cent_closed _).isClosedEmbedding_subtypeVal), (hUO _ νi hνi).2 t2⟩
    (fun v => ⟨uV v, ((l2 v).comp (cent_closed _).isClosedEmbedding_subtypeVal), (hUO _ (nv v) (hnv v)).2 (t3 v)⟩)
    S a b ha hb hEE hET
    (mapGL n (galAd σ)) (mapGL n (galInf σ)) (fun v => mapGL n (galFin σ v)) c1 c2 g1 g2
    (AdelicGLn.diagonal E n δ) (zA E n) hZ
    (fun v s => (hCL E n ⟨Real.exp s, Real.exp_pos s⟩).2.2.2 F v)
    (fun t => (hN3 F E σ hσ n hn δ γ hγ hδ _).2 ⟨t.1, Subgroup.mem_centralizer_singleton_iff.1 t.2, rfl⟩)
    (fun D hD => by
      obtain ⟨C, hC, hCx⟩ := (hP2 F E σ hσ n hn).2 (pI F n (AdelicGLn.diagonal F n γ)) (pI E n (AdelicGLn.diagonal E n δ))
        (hSL F n γ hγ).1 (hLN F E σ hσ n hn δ γ hδ).1 D hD
      refine ⟨C, hC, fun x hx => ?_⟩
      obtain ⟨t, ht, y, hy, rfl⟩ := hCx x hx
      exact ⟨⟨t, Subgroup.mem_centralizer_singleton_iff.2 ht⟩, y, hy, rfl⟩)
    (fun D hD => hBE F E σ hσ n hn (pI E n (AdelicGLn.diagonal E n δ)) D hD)
    φi φ hφi hφc hφ
    (fun v hv => by
      obtain ⟨e, hx⟩ := hS v hv
      refine ⟨e, fun x => ⟨fun h => ?_, ?_⟩⟩
      · obtain ⟨t, ht, y, hy, rfl⟩ := (hx x).1 h
        exact ⟨⟨t, Subgroup.mem_centralizer_singleton_iff.2 ht⟩, y, hy, rfl⟩
      · rintro ⟨t, y, hy, rfl⟩
        exact (hx _).2 ⟨t.1, Subgroup.mem_centralizer_singleton_iff.1 t.2, y, hy, rfl⟩)
  have hc : ∀ (s : ℝ) (x : GL (Fin n) (InfiniteAdeleRing E)),
      x⁻¹ * (pI E n (zA E n s) * pI E n (AdelicGLn.diagonal E n δ)) * mapGL n (galInf σ) x =
        pI E n (zA E n s) * (x⁻¹ * pI E n (AdelicGLn.diagonal E n δ) * mapGL n (galInf σ) x) := by
    intro s x
    have h := (hCL E n ⟨Real.exp s, Real.exp_pos s⟩).2.1 x⁻¹
    rw [← mul_assoc x⁻¹, ← h]
    simp only [mul_assoc]
  refine ⟨key.1, ?_⟩
  simp only [hc]
  exact key.2
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.RestrictedProductExtensionOfBaseRegroup
section
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4
open Filter

namespace UpperTheory.ConvolutionTheory.T4.RPGroup

section
universe u
variable {W V : Type} {I : V → Type}

private theorem exists_fam (ι : ∀ v, I v → W) (b : W → V) (hb : ∀ v i, b (ι v i) = v)
    (hinj : ∀ v, Function.Injective (ι v)) (hs : ∀ w, ∃ v i, ι v i = w)
    {X : W → Type u} (T : ∀ v (i : I v), X (ι v i)) :
    ∃ f : ∀ w, X w, ∀ v i, f (ι v i) = T v i := by
  have h : ∀ w, ∃ x : X w, ∀ v i (h : ι v i = w), h ▸ T v i = x := by
    intro w
    obtain ⟨v, i, rfl⟩ := hs w
    refine ⟨T v i, fun v' i' h => ?_⟩
    have hv : v' = v := by rw [← hb v' i', h, hb]
    subst hv
    have hi : i' = i := hinj v' h
    subst hi
    rfl
  choose f hf using h
  exact ⟨f, fun v i => (hf _ v i rfl).symm⟩

private theorem ev_up [∀ v, Finite (I v)] (ι : ∀ v, I v → W) (b : W → V) (hb : ∀ v i, b (ι v i) = v)
    {P : W → Prop} (h : ∀ᶠ w in cofinite, P w) : ∀ᶠ v in cofinite, ∀ i, P (ι v i) := by
  rw [eventually_cofinite] at h ⊢
  refine (h.image b).subset fun v hv => ?_
  simp only [Set.mem_setOf_eq, not_forall] at hv
  obtain ⟨i, hi⟩ := hv
  exact ⟨ι v i, hi, hb v i⟩

private theorem ev_down [∀ v, Finite (I v)] (ι : ∀ v, I v → W) (b : W → V) (hb : ∀ v i, b (ι v i) = v)
    (hs : ∀ w, ∃ v i, ι v i = w) {P : V → Prop} (h : ∀ᶠ v in cofinite, P v) :
    ∀ᶠ w in cofinite, P (b w) := by
  rw [eventually_cofinite] at h ⊢
  refine (h.biUnion fun v _ => Set.finite_range (ι v)).subset fun w hw => ?_
  obtain ⟨v, i, rfl⟩ := hs w
  simp only [Set.mem_setOf_eq, hb] at hw
  exact Set.mem_biUnion hw ⟨i, rfl⟩

variable {G Gi : Type} {H : W → Type} {Gv : V → Type} [Group G] [Group Gi] [∀ w, Group (H w)]
  [∀ v, Group (Gv v)] [TopologicalSpace G] [TopologicalSpace Gi] [∀ w, TopologicalSpace (H w)]
  [∀ v, TopologicalSpace (Gv v)] [T2Space Gi] [∀ v, T2Space (Gv v)]

private theorem rp_group [∀ v, Finite (I v)] {q : G →* Gi} {p : ∀ w, G →* H w} {K : ∀ w, Subgroup (H w)}
    (hRP : RP q p K) (ι : ∀ v, I v → W) (b : W → V) (hb : ∀ v i, b (ι v i) = v)
    (hinj : ∀ v, Function.Injective (ι v)) (hs : ∀ w, ∃ v i, ι v i = w)
    (e : ∀ v, Gv v ≃ₜ* ∀ i : I v, H (ι v i)) (p' : ∀ v, G →* Gv v) (K' : ∀ v, Subgroup (Gv v))
    (hp : ∀ v i g, e v (p' v g) i = p (ι v i) g)
    (hK : ∀ v x, x ∈ K' v ↔ ∀ i, e v x i ∈ K (ι v i)) : RP q p' K' := by
  have hcp : ∀ v, Continuous (p' v) := by
    intro v
    have h : ⇑(p' v) = fun g => (e v).symm (fun i => p (ι v i) g) := by
      funext g
      apply (e v).injective
      rw [ContinuousMulEquiv.apply_symm_apply]
      exact funext fun i => hp v i g
    rw [h]
    exact (e v).symm.continuous.comp (continuous_pi fun i => hRP.cp _)
  have hKset : ∀ v, (K' v : Set (Gv v)) = e v ⁻¹' Set.pi Set.univ fun i => (K (ι v i) : Set _) := by
    intro v
    ext x
    simp only [SetLike.mem_coe, hK, Set.mem_preimage, Set.mem_pi, Set.mem_univ, true_imp_iff]
  refine ⟨hRP.cq, hcp, fun v => ?_, fun v => ?_, fun g => ?_, fun S => ?_, fun g g' hq h => ?_,
    fun gi gv hgv => ?_, fun Ci C hCi hC hev => ?_⟩
  · rw [hKset]
    exact (isOpen_set_pi Set.finite_univ fun i _ => hRP.opn _).preimage (e v).continuous
  · have h : (K' v : Set (Gv v)) = (e v).symm '' Set.pi Set.univ fun i => (K (ι v i) : Set _) := by
      rw [hKset]
      ext x
      constructor
      · intro hx
        exact ⟨e v x, hx, (e v).symm_apply_apply x⟩
      · rintro ⟨y, hy, rfl⟩
        simpa [Set.mem_preimage] using hy
    rw [h]
    exact (isCompact_univ_pi fun i => hRP.cpt _).image (e v).symm.continuous
  · refine (ev_up ι b hb (hRP.ae g)).mono fun v h => ?_
    rw [hK]
    intro i
    rw [hp]
    exact h i
  · have hfin : (⋃ v ∈ (S : Set V), Set.range (ι v)).Finite :=
      S.finite_toSet.biUnion fun v _ => Set.finite_range (ι v)
    have hmem : ∀ w, w ∈ hfin.toFinset ↔ b w ∈ S := by
      intro w
      rw [Set.Finite.mem_toFinset]
      constructor
      · intro h
        obtain ⟨v, hv, i, rfl⟩ := Set.mem_iUnion₂.1 h
        rw [hb]
        exact hv
      · intro h
        obtain ⟨v, i, rfl⟩ := hs w
        rw [hb] at h
        exact Set.mem_biUnion h ⟨i, rfl⟩
    have h : (US p' K' S : Set G) = US p K hfin.toFinset := by
      ext g
      simp only [SetLike.mem_coe, mem_US]
      constructor
      · intro h w hw
        obtain ⟨v, i, rfl⟩ := hs w
        have hv : v ∉ S := by
          rw [hmem, hb] at hw
          exact hw
        have := (hK v _).1 (h v hv) i
        rwa [hp] at this
      · intro h v hv
        rw [hK]
        intro i
        rw [hp]
        exact h _ (by rw [hmem, hb]; exact hv)
    rw [h]
    exact hRP.opnU _
  · refine hRP.ext g g' hq fun w => ?_
    obtain ⟨v, i, rfl⟩ := hs w
    rw [← hp, ← hp, h]
  · obtain ⟨gw, hgw⟩ := exists_fam ι b hb hinj hs (X := H) fun v i => e v (gv v) i
    have hae : ∀ᶠ w in cofinite, gw w ∈ K w := by
      refine (ev_down ι b hb hs hgv).mono fun w h => ?_
      obtain ⟨v, i, rfl⟩ := hs w
      rw [hb] at h
      rw [hgw]
      exact (hK v _).1 h i
    obtain ⟨g, hq, hpg⟩ := hRP.surj gi gw hae
    refine ⟨g, hq, fun v => (e v).injective (funext fun i => ?_)⟩
    rw [hp, hpg, hgw]
  · obtain ⟨D, hD⟩ := exists_fam ι b hb hinj hs (X := fun w => Set (H w))
      fun v i => (fun x => e v x i) '' C v
    have hDc : ∀ w, IsCompact (D w) := by
      intro w
      obtain ⟨v, i, rfl⟩ := hs w
      rw [hD]
      exact (hC v).image ((continuous_apply i).comp (e v).continuous)
    have hDe : ∀ᶠ w in cofinite, D w ⊆ K w := by
      refine (ev_down ι b hb hs hev).mono fun w h => ?_
      obtain ⟨v, i, rfl⟩ := hs w
      rw [hb] at h
      rw [hD]
      rintro _ ⟨x, hx, rfl⟩
      exact (hK v x).1 (h hx) i
    have hA := hRP.prop Ci D hCi hDc hDe
    have hcl : IsClosed {g | q g ∈ Ci ∧ ∀ v, p' v g ∈ C v} := by
      have h : {g | q g ∈ Ci ∧ ∀ v, p' v g ∈ C v} = q ⁻¹' Ci ∩ ⋂ v, p' v ⁻¹' C v := by
        ext g
        simp
      rw [h]
      exact (hCi.isClosed.preimage hRP.cq).inter
        (isClosed_iInter fun v => (hC v).isClosed.preimage (hcp v))
    refine hA.of_isClosed_subset hcl ?_
    rintro g ⟨h1, h2⟩
    refine ⟨h1, fun w => ?_⟩
    obtain ⟨v, i, rfl⟩ := hs w
    rw [hD, ← hp]
    exact ⟨_, h2 v, rfl⟩

end

end UpperTheory.ConvolutionTheory.T4.RPGroup

open GroundTheory.Global GroundTheory.Global.SemiLocal GroundTheory.Global.AdeleBaseChange GroundTheory.Automorphic in
theorem UpperTheory.restrictedProduct_extension_of_base_regroup :
    RPF → RPE := by
  intro hF F E _ _ _ _ _ n
  refine UpperTheory.ConvolutionTheory.T4.RPGroup.rp_group (I := fun v : Pl F => PlacesOver E v) (hF E n)
    (fun v i => i.1) (below F) (fun v i => (below_eq_iff i.1 v).2 i.2)
    (fun v => Subtype.val_injective)
    (fun w => ⟨below F w, ⟨w, (below_eq_iff w _).1 rfl⟩, rfl⟩)
    (fun v => glPiEquiv (Fin n) fun w : PlacesOver E v => w.1.adicCompletion E)
    (fun v => pE E n v) (fun v => KE E n v) ?_ ?_
  · intro v i g
    refine Units.ext ?_
    ext a b
    rfl
  · intro v x
    have h : ∀ w : PlacesOver E v,
        mapGL n (Pi.evalRingHom (fun w : PlacesOver E v => w.1.adicCompletion E) w) x =
          glPiEquiv (Fin n) (fun w : PlacesOver E v => w.1.adicCompletion E) x w := by
      intro w
      refine Units.ext ?_
      ext a b
      rfl
    change (∀ w : PlacesOver E v, _ ∈ _) ↔ _
    exact forall_congr' fun w => by rw [h w]
end

-- bundled from Development.AutomorphicArithmetic.AdelicQuotients.SeparableLocalOfSeparableScalar
section
open PositivityTheory.Rg.Tf.Geo UpperTheory.ConvolutionTheory.G UpperTheory.ConvolutionTheory.T4

open NumberField GroundTheory.Automorphic GroundTheory.Automorphic.Reduction in
theorem UpperTheory.separableLocal_of_separableScalar :
    SepSc → CentLoc → SepLoc := by
  intro hS hC F _ _ n γ hγ
  have hsep : (γ : Matrix (Fin n) (Fin n) F).charpoly.Separable := hγ
  have hI : ((pI F n (AdelicGLn.diagonal F n γ)).val : Matrix (Fin n) (Fin n) (InfiniteAdeleRing F)) =
      (γ : Matrix (Fin n) (Fin n) F).map (algebraMap F (InfiniteAdeleRing F)) := by
    ext a b
    rfl
  have hIs : (pI F n (AdelicGLn.diagonal F n γ)).val.charpoly.Separable := by
    rw [hI, Matrix.charpoly_map]
    exact hsep.map
  refine ⟨hIs, fun s => ?_, fun v => ?_⟩
  · obtain ⟨⟨r, hr⟩, -⟩ := hC F n ⟨Real.exp s, Real.exp_pos s⟩
    have h := hr (pI F n (AdelicGLn.diagonal F n γ))
    have h' : (pI F n (zA F n s) * pI F n (AdelicGLn.diagonal F n γ)).val =
        (r : InfiniteAdeleRing F) • (pI F n (AdelicGLn.diagonal F n γ)).val := h
    rw [h']
    exact hS _ n r _ hIs
  · have hv : ((finAt v (AdelicGLn.diagonal F n γ)).val : Matrix (Fin n) (Fin n) (v.adicCompletion F)) =
        (γ : Matrix (Fin n) (Fin n) F).map (algebraMap F (v.adicCompletion F)) := by
      ext a b
      rfl
    rw [hv, Matrix.charpoly_map]
    exact hsep.map
end

