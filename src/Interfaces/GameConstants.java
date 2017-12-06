package Interfaces;

import java.awt.Color;

import ServerController.MyButtonListener;
import ServerController.MyCardListener;
import View.InfoPanel;


public interface GameConstants extends UNOConstants {

	/*@ public constraint \old(TOTAL_CARDS) == TOTAL_CARDS;
	  @*/
	/*@ spec_public @*/ int TOTAL_CARDS = 108;

	/*@ public constraint \old(FIRSTHAND) == FIRSTHAND;
	  @*/
	/*@ spec_public @*/ int FIRSTHAND = 8;

	/*@ public constraint \old(UNO_COLORS) == UNO_COLORS;
	  @ public invariant UNO_COLORS != null && ((Object[]) UNO_COLORS).length == 4;
	  @ public invariant (\forall int i; 0 <= i && i < ((Object[]) UNO_COLORS).length;
	  @ 	((Object[]) UNO_COLORS)[i] != null);
	  @*/
	/*@ spec_public nullable @*/ Color[] UNO_COLORS = { RED, BLUE, GREEN, YELLOW };

	/*@ public constraint \old(WILD_CARDCOLOR) == WILD_CARDCOLOR;
	  @ public invariant WILD_CARDCOLOR != null;
	  @ public invariant WILD_CARDCOLOR == BLACK;
	  @*/
	/*@ spec_public @*/ Color WILD_CARDCOLOR = BLACK;

	/*@ public constraint \old(UNO_NUMBERS) == UNO_NUMBERS;
	  @ public invariant UNO_NUMBERS != null && UNO_NUMBERS.length == 10;
	  @ public invariant (\forall int i; 0 <= i && i < UNO_NUMBERS.length;
	  @ 	UNO_NUMBERS[i] == i);
	  @*/
	/*@ spec_public @*/ int[] UNO_NUMBERS = { 0,1,2,3,4,5,6,7,8,9 };

	/*@ public constraint \old(ActionTypes) == ActionTypes;
	  @ public invariant ActionTypes != null && ActionTypes.length == 3;
	  @ public invariant (\forall int i; 0 <= i && i < ActionTypes.length; ActionTypes[i] != null);
	  @*/
	/*@ spec_public @*/ String[] ActionTypes = { REVERSE, SKIP, DRAW2PLUS };

	/*@ public constraint \old(WildTypes) == WildTypes;
	  @ public invariant WildTypes != null && WildTypes.length == 2;
	  @ public invariant (\forall int i; 0 <= i && i < WildTypes.length; WildTypes[i] != null);
	  @*/
	/*@ spec_public @*/ String[] WildTypes = { W_COLORPICKER, W_DRAW4PLUS };

	/*@ public constraint \old(vsPC) == vsPC;
	  @ public invariant vsPC == 1;
	  @*/
	/*@ spec_public @*/ int vsPC = 1;

	/*@ public constraint \old(MANUAL) == MANUAL;
	  @ public invariant MANUAL == 2;
	  @*/
	/*@ spec_public @*/ int MANUAL = 2;

	/*@ public constraint \old(GAMEMODES) == GAMEMODES;
	  @ public invariant GAMEMODES != null && GAMEMODES.length == 2;
	  @ public invariant (\forall int i; 0 <= i && i < GAMEMODES.length; GAMEMODES[i] == i + 1);
	  @*/
	/*@ spec_public @*/ int[] GAMEMODES = { vsPC, MANUAL };

	/*@ public constraint \old(CARDLISTENER) == CARDLISTENER;
	  @ public invariant CARDLISTENER != null;
	  @*/
	/*@ spec_public @*/ MyCardListener CARDLISTENER = new MyCardListener();

	/*@ public constraint \old(BUTTONLISTENER) == BUTTONLISTENER;
	  @ public invariant BUTTONLISTENER != null;
	  @*/
	/*@ spec_public @*/ MyButtonListener BUTTONLISTENER = new MyButtonListener();

	/*@ public constraint \old(infoPanel) == infoPanel;
	  @ public invariant infoPanel != null;
	  @*/
	/*@ spec_public @*/ InfoPanel infoPanel = new InfoPanel();
}
