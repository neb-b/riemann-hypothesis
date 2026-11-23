module

public import Development.EtaleCohomology.EtaleSheaves.Bundle0005
public import Development.EtaleCohomology.EtaleSheaves.LineHigh
public import Development.EtaleCohomology.EtaleSheaves.Bundle0008
public import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0007
public import Development.EtaleCohomology.EtaleSheaves.Bundle0007

@[expose] public section

-- bundled from Development.EtaleCohomology.EtaleSheaves.StalkCut
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.StalkCut

def RelZ (q : ℕ) (i n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) : Prop :=
  (∀ m : ℤ, m + 1 = n → Function.Surjective (pull _ (sch.map (Spec.map f)) (tw q i) m)) ∧
  Function.Injective (pull _ (sch.map (Spec.map f)) (tw q i) n)

def BCn (q : ℕ) (i n : ℤ) {A Y C : CommRingCat.{0}} (φ : A ⟶ Y) (c : A ⟶ C) : Prop :=
  ∀ (Y' : CommRingCat.{0}) (w : Y ⟶ Y') (φ' : C ⟶ Y'), IsPushout φ c w φ' → RelZ q i n φ'

def PushClosed {A : CommRingCat.{0}} (P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop) : Prop :=
  ∀ {C D E Z : CommRingCat.{0}} (c : A ⟶ C) (f : C ⟶ D) (g : C ⟶ E) (u : D ⟶ Z) (v : E ⟶ Z), IsPushout f g u v →
    P C c → P D (c ≫ f) → P E (c ≫ g) → P Z (c ≫ f ≫ u)

def EtClosed {A : CommRingCat.{0}} (P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop) : Prop :=
  ∀ {C D : CommRingCat.{0}} (c : A ⟶ C) (f : C ⟶ D), P C c → Et f → P D (c ≫ f)

theorem relZ_neg (hH : Hyp) (q : ℕ) (i n : ℤ) {A B : CommRingCat.{0}} (f : A ⟶ B) (hn : n < 0) : RelZ q i n f := by
  have hA9 := (hH.2.2.2.2.2.1 (ZMod q) (tw q i)).1
  refine ⟨fun m hm y => ?_, fun x y _ => ?_⟩
  · haveI := hA9 (sch.obj (Spec B)) m (by omega)
    exact ⟨0, Subsingleton.elim _ _⟩
  · haveI := hA9 (sch.obj (Spec A)) n hn
    exact Subsingleton.elim _ _

theorem re_of_relZ {q : ℕ} {i : ℤ} {A B : CommRingCat.{0}} {f : A ⟶ B} (h : ∀ n, RelZ q i n f) : RE q i f :=
  fun m => ⟨(h m).2, (h (m + 1)).1 m rfl⟩

def DescInt : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ {C D : CommRingCat.{0}} (c : A ⟶ C) (g : C ⟶ D), P C c → P D (c ≫ g) → g.hom.IsIntegral → SpS g →
  BCn q i n φ (c ≫ g) → BCn q i n φ c

def DescLoc : Prop := Hyp → ∀ (q : ℕ) [NeZero q] (i n : ℤ) {A Y : CommRingCat.{0}} (φ : A ⟶ Y), IsUnit (q : A) →
  ∀ P : ∀ C : CommRingCat.{0}, (A ⟶ C) → Prop, PushClosed P → EtClosed P →
  (∀ m < n, ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c) →
  ∀ (D : CommRingCat.{0}) (d : A ⟶ D), P D d →
  (∀ r : Ideal D, r.IsPrime → ∃ (O : CommRingCat.{0}) (o : D ⟶ O) (Q : Ideal O), IE o ∧ Q.IsPrime ∧ Q.comap o.hom = r ∧
    BC q i φ (d ≫ o)) →
  BCn q i n φ d

theorem goal_of (hInt : DescInt) (hLoc : DescLoc) : LateralTheory.E.t_E3Cut.Stalk := by
  intro hH q _ i A Y φ hq P hpush het hcov C c hC
  have key : ∀ k : ℕ, ∀ m : ℤ, m < k → ∀ (C : CommRingCat.{0}) (c : A ⟶ C), P C c → BCn q i m φ c := by
    intro k
    induction k with
    | zero =>
      intro m hm C c _ Y' w φ' _
      exact relZ_neg hH q i m φ' (by exact_mod_cast hm)
    | succ k ih =>
      intro m hm C c hC
      have hm' : m ≤ (k : ℤ) := by push_cast at hm; omega
      rcases lt_or_eq_of_le hm' with h | h
      · exact ih m h C c hC
      · subst h
        obtain ⟨D, g, hgi, hgs, hD, hpts⟩ := hcov C c hC
        have hDl : BCn q i (k : ℤ) φ (c ≫ g) :=
          hLoc hH q i k φ hq P @hpush @het ih D (c ≫ g) hD (fun r hr => by
            obtain ⟨O, o, Q, h1, h2, h3, h4⟩ := hpts r hr
            exact ⟨O, o, Q, h1, h2, h3, by rwa [Category.assoc]⟩)
        exact hInt hH q i k φ hq P @hpush ih c g hC hD hgi hgs hDl
  intro Y' w φ' hpo
  refine re_of_relZ fun n => ?_
  exact key (n.toNat + 1) n (by omega) C c hC Y' w φ' hpo

end LateralTheory.E.StalkCut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.StalkGerm
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut

namespace LateralTheory.E.ZLGPf

variable {Y X S : Scheme.{0}}

abbrev overO (p : X ⟶ S) (U : S.Opens) : Scheme.{0} := pullback p U.ι

abbrev resO (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) : overO p V ⟶ overO p U :=
  pullback.map p V.ι p U.ι (𝟙 _) (S.homOfLE h) (𝟙 _) (by simp) (by simp)

abbrev fO (f : Y ⟶ X) (p : X ⟶ S) (U : S.Opens) : overO (f ≫ p) U ⟶ overO p U :=
  pullback.map (f ≫ p) U.ι p U.ι f (𝟙 _) (𝟙 _) (by simp) (by simp)

def Germ (q : ℕ) (i n : ℤ) (f : Y ⟶ X) (p : X ⟶ S) (s : S) : Prop :=
  (∀ (U : S.Opens), s ∈ U → ∀ x : Ht q (sch.obj (overO p U)) n i, pull _ (sch.map (fO f p U)) _ _ x = 0 →
    ∃ (V : S.Opens) (h : V ≤ U), s ∈ V ∧ pull _ (sch.map (resO p h)) _ _ x = 0) ∧
  (∀ (U : S.Opens), s ∈ U → ∀ y : Ht q (sch.obj (overO (f ≫ p) U)) n i,
    ∃ (V : S.Opens) (h : V ≤ U), s ∈ V ∧ ∃ x : Ht q (sch.obj (overO p V)) n i,
      pull _ (sch.map (fO f p V)) _ _ x = pull _ (sch.map (resO (f ≫ p) h)) _ _ y)

def StalkGerm : Prop := Cont → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [CompactSpace S]
  [QuasiSeparatedSpace S] [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f],
  IsUnit (q : Γ(S, ⊤)) → ∀ i : ℤ, ∀ s : S,
  Eqv _ (sch.map (pullback.map (f ≫ p) (S.fromSpecStalk s) p (S.fromSpecStalk s) f (𝟙 _) (𝟙 _) (by simp) (by simp))) (tw q i) →
  ∀ n : ℤ, Germ q i n f p s

def ZarInd : Prop := MV → Hyp → ∀ (q : ℕ) {Y X S : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) [CompactSpace S]
  [QuasiSeparatedSpace S] [QuasiCompact p] [QuasiSeparated p] [QuasiCompact f] [QuasiSeparated f],
  IsUnit (q : Γ(S, ⊤)) → ∀ i : ℤ, (∀ (s : S) (n : ℤ), Germ q i n f p s) → Eqv _ (sch.map f) (tw q i)

theorem ZLG_of (hC : Cont) (hM : MV) (h1 : StalkGerm) (h2 : ZarInd) : ZLG := by
  intro hH q Y X S f p _ _ _ _ _ _ hq i hs
  exact h2 hM hH q f p hq i fun s n => h1 hC hH q f p hq i s (hs s) n

end LateralTheory.E.ZLGPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.StdCoverPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.StdCoverPf

theorem mono_spMap {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B)
    [Mono (Spec.map (CommRingCat.ofHom φ))] : Mono (spMap φ) := by
  have h : Mono (yoneda.map (Spec.map (CommRingCat.ofHom φ))) := inferInstance
  haveI : ∀ X, Mono ((spMap φ).app X) := fun _ => h
  exact NatTrans.mono_of_mono_app _

abbrev Xs {S : Type} [CommRing S] (f g : S) (b : Bool) : Scheme.{0} :=
  Spec (CommRingCat.of (Localization.Away (bif b then f else g)))

abbrev ι {S : Type} [CommRing S] (f g : S) (b : Bool) : Xs f g b ⟶ Spec (CommRingCat.of S) :=
  Spec.map (CommRingCat.ofHom (algebraMap S (Localization.Away (bif b then f else g))))

theorem cover_mem {S : Type} [CommRing S] (f g : S) (hfg : Ideal.span {f, g} = ⊤) :
    Sieve.ofArrows (Xs f g) (ι f g) ∈ Scheme.etaleTopology.{0} (Spec (CommRingCat.of S)) := by
  apply Precoverage.generate_mem_toGrothendieck
  refine (Scheme.ofArrows_mem_precoverage_iff (P := @Etale) (f := ι f g)).2 ⟨fun pt => ?_, fun b => inferInstance⟩
  let p : PrimeSpectrum S := pt
  have hp : f ∉ p.asIdeal ∨ g ∉ p.asIdeal := by
    by_contra hc
    push_neg at hc
    have : Ideal.span {f, g} ≤ p.asIdeal := by
      rw [Ideal.span_le]; intro z hz
      rcases hz with rfl | hz
      · exact hc.1
      · rw [Set.mem_singleton_iff] at hz; exact hz ▸ hc.2
    rw [hfg] at this
    exact p.isPrime.ne_top (top_le_iff.mp this)
  rcases hp with h | h
  · have hm : p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away f))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away f) f]; exact h
    obtain ⟨q, hq⟩ := hm
    exact ⟨true, q, hq⟩
  · have hm : p ∈ Set.range (PrimeSpectrum.comap (algebraMap S (Localization.Away g))) := by
      rw [PrimeSpectrum.localization_away_comap_range (Localization.Away g) g]; exact h
    obtain ⟨q, hq⟩ := hm
    exact ⟨false, q, hq⟩

theorem key (R : Type) [CommRing R] (S : Type) [CommRing S] (f g : S) (hfg : Ideal.span {f, g} = ⊤) {G : Shv R}
    (u v : (free R).obj (yoneda.obj (Spec (CommRingCat.of S))) ⟶ G)
    (hb : ∀ b, (free R).map (yoneda.map (ι f g b)) ≫ u = (free R).map (yoneda.map (ι f g b)) ≫ v) : u = v := by
  let adj := sheafificationAdjunction Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))
  apply (adj.homEquiv ((freeP R).obj (yoneda.obj (Spec (CommRingCat.of S)))) G).injective
  have hb' : ∀ b, (freeP R).map (yoneda.map (ι f g b)) ≫ adj.homEquiv _ G u =
      (freeP R).map (yoneda.map (ι f g b)) ≫ adj.homEquiv _ G v := by
    intro b
    have h0 : (presheafToSheaf _ _).map ((freeP R).map (yoneda.map (ι f g b))) ≫ u =
        (presheafToSheaf _ _).map ((freeP R).map (yoneda.map (ι f g b))) ≫ v := hb b
    have h1 := congrArg (adj.homEquiv _ G) h0
    erw [adj.homEquiv_naturality_left, adj.homEquiv_naturality_left] at h1
    exact h1
  generalize adj.homEquiv _ G u = u' at hb' ⊢
  generalize adj.homEquiv _ G v = v' at hb' ⊢
  ext X : 2
  apply ModuleCat.free_hom_ext
  intro x0
  have hT := Scheme.etaleTopology.pullback_stable x0.down (cover_mem f g hfg)
  have e := G.property.hom_ext ⟨_, hT⟩
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ (u'.app X (ModuleCat.freeMk x0))))
    (ModuleCat.ofHom (LinearMap.toSpanSingleton (ULift.{1} R) _ (v'.app X (ModuleCat.freeMk x0)))) ?_
  · have := congrArg (fun e => e.hom 1) e
    simp only [ModuleCat.hom_ofHom, LinearMap.toSpanSingleton_apply, one_smul] at this
    exact this
  rintro ⟨W, k, hk⟩
  obtain ⟨Z, h, _, ⟨b⟩, hh⟩ := hk
  ext1
  apply LinearMap.ext_ring
  simp only [ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.coe_comp, Function.comp_apply,
    LinearMap.toSpanSingleton_apply, one_smul]
  have hm : (((freeP R).obj (yoneda.obj (Spec (CommRingCat.of S)))).map k.op).hom (ModuleCat.freeMk x0) =
      (((freeP R).map (yoneda.map (ι f g b))).app (op W)).hom (ModuleCat.freeMk (ULift.up h)) := by
    simp only [freeP, ModuleCat.freeMk]
    erw [Finsupp.lmapDomain_apply, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single, Finsupp.mapDomain_single]
    change Finsupp.single (ULift.up (k ≫ x0.down)) _ = Finsupp.single (ULift.up (h ≫ ι f g b)) _
    rw [hh]
  change ((u'.app X ≫ (G.obj.map k.op)).hom (ModuleCat.freeMk x0)) =
    ((v'.app X ≫ (G.obj.map k.op)).hom (ModuleCat.freeMk x0))
  erw [← u'.naturality, ← v'.naturality]
  change (u'.app (op W)).hom ((((freeP R).obj (yoneda.obj (Spec (CommRingCat.of S)))).map k.op).hom (ModuleCat.freeMk x0)) =
    (v'.app (op W)).hom ((((freeP R).obj (yoneda.obj (Spec (CommRingCat.of S)))).map k.op).hom (ModuleCat.freeMk x0))
  rw [hm]
  change ((((freeP R).map (yoneda.map (ι f g b))) ≫ u').app (op W)).hom (ModuleCat.freeMk (ULift.up h)) =
    ((((freeP R).map (yoneda.map (ι f g b))) ≫ v').app (op W)).hom (ModuleCat.freeMk (ULift.up h))
  rw [hb' b]

theorem epi_cover (R : Type) [CommRing R] (S : Type) [CommRing S] (f g : S) (hfg : Ideal.span {f, g} = ⊤)
    (n : SimplexCategoryᵒᵖ) :
    Epi (biprod.desc ((free R).map ((spMap (algebraMap S (Localization.Away f))).app n))
      ((free R).map ((spMap (algebraMap S (Localization.Away g))).app n))) := by
  constructor
  intro G u v h
  have hf := congrArg (biprod.inl ≫ ·) h
  have hg := congrArg (biprod.inr ≫ ·) h
  simp only [biprod.inl_desc_assoc, biprod.inr_desc_assoc] at hf hg
  exact key R S f g hfg u v (fun b => by cases b; exacts [hg, hf])

end LateralTheory.E.StdCoverPf

open LateralTheory.E.StdCoverPf in
theorem LateralTheory.E.MVPf.StdCover_of : LateralTheory.E.MVPf.StdCover := by
  intro R _ S _ f g hfg
  exact ⟨mono_spMap _, mono_spMap _, epi_cover R S f g hfg⟩
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.SteinPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC

namespace LateralTheory.E.SteinPf
open LateralTheory.E.t_E2Cut

def RelNorm : Prop := ∀ {Z S : Scheme.{0}} (g : Z ⟶ S) [QuasiCompact g] [QuasiSeparated g], AICSch Z →
  ∃ (T : Scheme.{0}) (c : Z ⟶ T) (k : T ⟶ S), IsIntegral T ∧ IsDominant c ∧ IsIntegralHom k ∧ c ≫ k = g ∧
    ∀ V : T.Opens, IsAffineOpen V → (V : Set T).Nonempty →
      ((c ⁻¹ᵁ V : Set Z).Nonempty ∧ Function.Injective (c.app V) ∧
        ∀ b : Γ(Z, c ⁻¹ᵁ V), (c.app V).hom.IsIntegralElem b → ∃ a, c.app V a = b)

def AICOpen : Prop := ∀ {Z : Scheme.{0}}, AICSch Z → ∀ W : Z.Opens, (W : Set Z).Nonempty → AIC Γ(Z, W)

theorem aic_of_int {A B : Type} [CommRing A] [CommRing B] (φ : A →+* B) (hB : AIC B) (hi : Function.Injective φ)
    (hc : ∀ b : B, φ.IsIntegralElem b → ∃ a, φ a = b) (hn : Nontrivial B) : AIC A := by
  intro p hm hd
  obtain ⟨b, hb⟩ := hB (p.map φ) (hm.map φ) (by rw [hm.natDegree_map]; exact hd)
  obtain ⟨a, rfl⟩ := hc b ⟨p, hm, by rwa [Polynomial.eval₂_eq_eval_map]⟩
  refine ⟨a, hi ?_⟩
  rw [map_zero, ← Polynomial.eval_map_apply]; exact hb

theorem Stein_of (hR : RelNorm) (hA : AICOpen) : Stein := by
  intro Z S g _ _ hZ
  obtain ⟨T, c, k, hT, hc, hk, hck, hV⟩ := hR g hZ
  refine ⟨T, c, k, ⟨hT, fun V hV' hne => ?_⟩, hc, hk, hck⟩
  obtain ⟨hne', hi, hcl⟩ := hV V hV' hne
  have hB := hA hZ _ hne'
  have : IsIntegral Z := hZ.1
  have : Nonempty (c ⁻¹ᵁ V) := hne'.to_subtype
  exact aic_of_int (c.app V).hom hB hi hcl inferInstance

end LateralTheory.E.SteinPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.StrictLocalStalks
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut

namespace LateralTheory.E.ULAStalkPf

def PolyPO : Prop := ∀ {A B : CommRingCat.{0}} (b : A ⟶ B),
  IsPushout (pC A) b (CommRingCat.ofHom (Polynomial.mapRingHom b.hom)) (pC B)

def IECob : Prop := ∀ {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (u : B ⟶ D) (v : C ⟶ D),
  IsPushout f g u v → IE f → IE v

def FracAIC : Prop := ∀ (T K : Type) [CommRing T] [IsDomain T] [Field K] [Algebra T K] [IsFractionRing T K], AIC T → AIC K

def FracOf : Prop := ∀ (B C : Type) [CommRing B] [CommRing C] [IsDomain C] (j : B →+* C), Function.Injective j →
  (∀ z : C, ∃ s y : B, s ≠ 0 ∧ j s * z = j y) →
  @IsFractionRing B _ (FractionRing C) _ ((algebraMap C (FractionRing C)).comp j).toAlgebra

theorem ULAStalk_of (hI : IntClos) (hT : SHTensor) (hA : AICSH) (hE : SHEqv) (hC3 : EtaleBaseChangeFractionFieldIndEtaleOverPolynomial)
    (p1 : PolyPO) (p2 : IECob) (p3 : FracAIC) (p4 : FracOf) : ULAStalk := by
  intro H q _ i A X h hq hA' hX hh hloc C c _ _ hCa hCr Y' w φ' sq
  obtain ⟨B, b, j, hbj, hbint, hjinj, hBloc, hBaic, hfr⟩ := hI c hA' hCa hCr
  have : IsDomain B := Function.Injective.isDomain j.hom hjinj
  let K := FractionRing C
  let l : C ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap C K)
  let algBK : Algebra B K := ((algebraMap C K).comp j.hom).toAlgebra
  have : IsFractionRing B K := p4 B C j.hom hjinj hfr
  have hKsh : SH K := hA K (p3 C K hCa)
  have hBsh : SH B := hA B hBaic
  have hCsh : SH C := hA C hCa
  have hqB : IsUnit (q : B) := by simpa using hq.map b.hom
  have hqC : IsUnit (q : C) := by simpa using hq.map c.hom

  let mB : CommRingCat.of (Polynomial A) ⟶ CommRingCat.of (Polynomial B) := CommRingCat.ofHom (Polynomial.mapRingHom b.hom)
  have sB : IsPushout h mB (pushout.inl h mB) (pushout.inr h mB) := IsPushout.of_hasPushout _ _
  have hBIE : IE (pushout.inr h mB) := p2 _ _ _ _ sB hh
  have sBA : IsPushout (pC A ≫ h) b (pushout.inl h mB) (pC B ≫ pushout.inr h mB) := (p1 b).paste_horiz sB
  let ZB : CommRingCat.{0} := pushout h mB
  have hZBsh : SH ZB := hT _ _ _ _ sBA hA' hX hloc hbint hBloc
  have r1 : RE q i (pC B ≫ pushout.inr h mB) := hE H q i _ hqB hBsh hZBsh
  let bl : B ⟶ CommRingCat.of K := CommRingCat.ofHom (algebraMap B K)
  have sL : IsPushout (pC B ≫ pushout.inr h mB) bl (pushout.inl _ bl) (pushout.inr _ bl) := IsPushout.of_hasPushout _ _
  have r2 : RE q i (pushout.inl (pC B ≫ pushout.inr h mB) bl) :=
    hC3 H q i B K hBaic hqB (pushout h mB) (pushout.inr h mB) hBIE _ _ _ sL.flip
  have r3 : RE q i bl := hE H q i bl hqB hBsh hKsh
  have r4 : RE q i (pushout.inr (pC B ≫ pushout.inr h mB) bl) :=
    RE.of_comp_left r3 (by rw [← pushout.condition]; exact r1.comp r2)

  let mC : CommRingCat.of (Polynomial A) ⟶ CommRingCat.of (Polynomial C) := CommRingCat.ofHom (Polynomial.mapRingHom c.hom)
  let hC : CommRingCat.of (Polynomial C) ⟶ Y' := (p1 c).desc (h ≫ w) φ' (by rw [← Category.assoc]; exact sq.w)
  have e1 : mC ≫ hC = h ≫ w := (p1 c).inl_desc _ _ _
  have e2 : pC C ≫ hC = φ' := (p1 c).inr_desc _ _ _
  have sC : IsPushout h mC w hC := IsPushout.of_left (by rw [e2]; exact sq) e1.symm (p1 c)
  have hCIE : IE hC := p2 _ _ _ _ sC hh
  have sq' : IsPushout l (pC C ≫ hC) (pushout.inr φ' l) (pushout.inl φ' l) := by
    rw [e2]; exact (IsPushout.of_hasPushout φ' l).flip
  have r5 : RE q i (pushout.inl φ' l) := hC3 H q i C K hCa hqC Y' hC hCIE _ _ _ sq'
  have r6 : RE q i l := hE H q i l hqC hCsh hKsh
  have ebl : b ≫ bl = c ≫ l := by rw [← hbj]; rfl
  have PZ : IsPushout (pC A ≫ h) (c ≫ l) (pushout.inl h mB ≫ pushout.inl (pC B ≫ pushout.inr h mB) bl)
      (pushout.inr (pC B ≫ pushout.inr h mB) bl) := by
    rw [← ebl]; exact sBA.paste_vert sL
  have PZ' : IsPushout (pC A ≫ h) (c ≫ l) (w ≫ pushout.inl φ' l) (pushout.inr φ' l) :=
    sq.paste_vert (IsPushout.of_hasPushout φ' l)
  have r7 : RE q i (pushout.inr φ' l) := by
    rw [← PZ.inr_isoIsPushout_hom _ _ PZ']; exact r4.comp (RE.of_isIso q i _)
  exact RE.of_comp_right r5 (by rw [pushout.condition]; exact r6.comp r7)

end LateralTheory.E.ULAStalkPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.UnitExistence
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.LeafOneExistsPf

open LateralTheory.E.CupProductRingLaws

def LeafUnitSec : Prop := ∀ (q : ℕ) [NeZero q], ∃ one : ∀ (U : Scheme.{0}), IsUnit (q : Γ(U, ⊤)) → Sec (tw q 0) U,
  (∀ (V U : Scheme.{0}) (g : V ⟶ U) (hU : IsUnit (q : Γ(U, ⊤))) (hV : IsUnit (q : Γ(V, ⊤))),
    Sec.res g (one U hU) = one V hV) ∧
  ∀ (U : Scheme.{0}) (hU : IsUnit (q : Γ(U, ⊤))) (ζ : Prim q Γ(U, ⊤)), one U hU = twGen 0 ζ

def LeafCocycleOfSec : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (E : Spc)
  (s : ∀ (U : Scheme.{0}), Nonempty (Sx E 0 U) → Sec F U),
  (∀ (V U : Scheme.{0}) (g : V ⟶ U) (hU : Nonempty (Sx E 0 U)) (hV : Nonempty (Sx E 0 V)), Sec.res g (s U hU) = s V hV) →
  ∃ α : Cocycle ((chains R).obj E) (res R F) 0,
    ∀ (U : Scheme.{0}) (x : Sx E 0 U), ev (R := R) α.1 0 0 (by simp) U x = Sec.map (resι R F) (s U ⟨x⟩)

theorem LeafOneExists_of (hU : LeafUnitSec) (hC : LeafCocycleOfSec) : LateralTheory.E.LeafOneSpecPf.LeafOneExists := by
  intro q _ E hE
  obtain ⟨one, hnat, hone⟩ := hU q
  obtain ⟨α, hα⟩ := hC (ZMod q) (tw q 0) E (fun U h => one U (hE U h))
    (fun V U g hU' hV' => hnat V U g _ _)
  refine ⟨α, fun U x ζ => ?_⟩
  rw [hα U x, hone U _ ζ]
  rfl

end LateralTheory.E.LeafOneExistsPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ZariskiLocalCech
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.ZariskiLocalCech

def CechSigma : Prop := t_E3Cut.Hyp → ∀ (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (g : Y ⟶ X) (O : X.Opens)
  {ι : Type} (V : ι → X.Opens), (∀ j, V j ≤ O) → O ≤ ⨆ j, V j →
  (∀ n : ℕ, Eqv R (sch.map (Limits.Sigma.map fun j : Fin (n + 1) → ι => g ∣_ (⨅ k, V (j k)))) F) →
  Eqv R (sch.map (g ∣_ O)) F

section
variable {R : Type} [CommRing R] {F : Shv R}

theorem eqv_comp {E E' E'' : Spc} {f : E ⟶ E'} {g : E' ⟶ E''} (hf : Eqv R f F) (hg : Eqv R g F) :
    Eqv R (f ≫ g) F := fun n => by
  have h : ⇑(pull R (f ≫ g) F n) = pull R f F n ∘ pull R g F n := funext fun x => pull_comp R f g F n x
  rw [h]; exact (hf n).comp (hg n)

theorem eqv_iso {E E' : Spc} (f : E ⟶ E') [IsIso f] : Eqv R f F := fun n => by
  have h1 : ∀ x, pull R (inv f) F n (pull R f F n x) = x := fun x => by
    rw [← pull_comp, IsIso.inv_hom_id, pull_id]
  have h2 : ∀ x, pull R f F n (pull R (inv f) F n x) = x := fun x => by
    rw [← pull_comp, IsIso.hom_inv_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

theorem sigmaEqv (hC : t_E3Cut.Coprod) {ι : Type} {Y X : ι → Scheme.{0}} (f : ∀ j, Y j ⟶ X j)
    (hf : ∀ j, Eqv R (sch.map (f j)) F) : Eqv R (sch.map (Limits.Sigma.map f)) F := fun n => by
  have key : (fun (x : H R (sch.obj (∐ X)) F n) (j : ι) => pull R (sch.map (Sigma.ι Y j)) F n
      (pull R (sch.map (Limits.Sigma.map f)) F n x)) =
      Pi.map (fun j => pull R (sch.map (f j)) F n) ∘
        (fun (x : H R (sch.obj (∐ X)) F n) (j : ι) => pull R (sch.map (Sigma.ι X j)) F n x) := by
    funext x j
    simp only [Function.comp_apply, Pi.map_apply]
    rw [← pull_comp, ← pull_comp, ← Functor.map_comp, ← Functor.map_comp, Sigma.ι_map]
  have hb := (Function.Bijective.piMap (fun j => hf j n)).comp (hC R F X n)
  rw [← key] at hb
  exact (Function.Bijective.of_comp_iff' (hC R F Y n) _).1 hb

theorem eqv_of_top {Y X : Scheme.{0}} (g : Y ⟶ X) (h : Eqv R (sch.map (g ∣_ ⊤)) F) : Eqv R (sch.map g) F := by
  have : IsIso (⊤ : X.Opens).ι := isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
  have : IsIso (g ⁻¹ᵁ ⊤).ι := isIso_of_isOpenImmersion_of_opensRange_eq_top _ (by simp)
  have e : g = inv (g ⁻¹ᵁ ⊤).ι ≫ (g ∣_ ⊤) ≫ (⊤ : X.Opens).ι := by
    rw [morphismRestrict_ι, IsIso.inv_hom_id_assoc]
  rw [e, Functor.map_comp, Functor.map_comp]
  exact eqv_comp (eqv_iso _) (eqv_comp h (eqv_iso _))

end

theorem inf_basicOpen {X : Scheme.{0}} {A : X.Opens} {κ : Type} [DecidableEq κ] (f : κ → Γ(X, A)) (s : Finset κ) :
    (s.inf fun k => X.basicOpen (f k)) ⊓ A = X.basicOpen (∏ k ∈ s, f k) := by
  induction s using Finset.induction_on with
  | empty => simp [X.basicOpen_of_isUnit isUnit_one]
  | insert a s ha ih =>
    rw [Finset.inf_insert, Finset.prod_insert ha, Scheme.basicOpen_mul, ← ih, inf_assoc]

theorem iInf_basicOpen {X : Scheme.{0}} {A : X.Opens} {n : ℕ} (f : Fin (n + 1) → Γ(X, A)) :
    (⨅ k, X.basicOpen (f k)) = X.basicOpen (∏ k, f k) := by
  rw [← inf_basicOpen f Finset.univ, Finset.inf_univ_eq_iInf]
  exact (inf_eq_left.2 ((iInf_le (fun k => X.basicOpen (f k)) 0).trans (X.basicOpen_le (f 0)))).symm

theorem ZarLocal_of (hCop : t_E3Cut.Coprod) (hCS : CechSigma) : t_E3Cut.ZarLocal := by
  intro hH R _ F Y X g hU
  choose U hxU hUe using hU
  have hA : ∀ x : X, ∃ A : X.Opens, IsAffineOpen A ∧ x ∈ A ∧ A ≤ U x := fun x => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open (hxU x) (U x).2
    exact ⟨V, hV, hxV, hVU⟩
  choose A hAaff hxA hAU using hA
  have st1 : ∀ (x : X) (O : X.Opens), O ≤ A x → Eqv R (sch.map (g ∣_ O)) F := by
    intro x O hO
    refine hCS hH R F g O (ι := {f : Γ(X, A x) // X.basicOpen f ≤ O}) (fun f => X.basicOpen f.1) (fun f => f.2) ?_ ?_
    · intro y hy
      obtain ⟨f, hfO, hyf⟩ := (hAaff x).exists_basicOpen_le ⟨y, hy⟩ (hO hy)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨f, hfO⟩, hyf⟩
    · intro n
      apply sigmaEqv hCop
      intro j
      have e := iInf_basicOpen (X := X) (A := A x) (fun k => (j k).1)
      apply hUe x
      · rw [e]; exact (hAaff x).basicOpen _
      · exact (iInf_le _ 0).trans ((X.basicOpen_le _).trans (hAU x))
  refine eqv_of_top g (hCS hH R F g ⊤ A (fun _ => le_top) ?_ ?_)
  · intro y _
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨y, hxA y⟩
  · exact fun n => sigmaEqv hCop _ fun j => st1 (j 0) _ (iInf_le _ 0)

end LateralTheory.E.ZariskiLocalCech
end
end

