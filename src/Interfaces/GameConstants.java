package Interfaces;

import java.awt.Color;

import ServerController.MyButtonListener;
import ServerController.MyCardListener;
import View.InfoPanel;


public interface GameConstants extends UNOConstants {

	/*@ spec_public @*/ int TOTAL_CARDS = 108;
	/*@ spec_public @*/ int FIRSTHAND = 8;

	/*@ spec_public @*/ Color[] UNO_COLORS = {RED, BLUE, GREEN, YELLOW};
	/*@ spec_public @*/ Color WILD_CARDCOLOR = BLACK;

	/*@ spec_public @*/ int[] UNO_NUMBERS =  {0,1,2,3,4,5,6,7,8,9};
	/*@ spec_public @*/ String[] ActionTypes = {REVERSE,SKIP,DRAW2PLUS};
	/*@ spec_public @*/ String[] WildTypes = {W_COLORPICKER, W_DRAW4PLUS};

	/*@ spec_public @*/ int vsPC = 1;
	/*@ spec_public @*/ int MANUAL = 2;

	/*@ spec_public @*/ int[] GAMEMODES = {vsPC, MANUAL};

	/*@ spec_public @*/ MyCardListener CARDLISTENER = new MyCardListener();
	/*@ spec_public @*/ MyButtonListener BUTTONLISTENER = new MyButtonListener();

	/*@ spec_public @*/ InfoPanel infoPanel = new InfoPanel();
}
