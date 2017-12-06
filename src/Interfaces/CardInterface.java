package Interfaces;

import java.awt.Color;
import java.awt.Dimension;

public interface CardInterface {

	/*@ public constraint \old(WIDTH) == WIDTH;
	  @*/
	/*@ spec_public @*/ int WIDTH = 50;

	/*@ public constraint \old(HEIGHT) == HEIGHT;
	  @*/
	/*@ spec_public @*/ int HEIGHT = 75;
	/*@ spec_public non_null @*/ Dimension SMALL = new Dimension(WIDTH, HEIGHT);
	/*@ spec_public non_null @*/ Dimension MEDIUM = new Dimension(WIDTH * 2, HEIGHT * 2);
	/*@ spec_public non_null @*/ Dimension BIG = new Dimension(WIDTH * 3, HEIGHT * 3);

	// Default card size
	/*@ public invariant CARDSIZE == MEDIUM;
	  @*/
	/*@ spec_public non_null @*/ Dimension CARDSIZE = MEDIUM;

	// Default offset
	/*@ public constraint \old(OFFSET) == OFFSET;
	  @*/
	/*@ spec_public @*/ int OFFSET = 71;

	/*@ requires newColor != null;
	  @*/
	void setColor(/*@ non_null @*/ Color newColor);

	/*@ ensures \result != null;
	  @*/
	/*@ pure @*/ Color getColor();

	/*@ requires newValue != null;
	  @*/
	void setValue(/*@ non_null @*/ String newValue);

	/*@ ensures \result != null;
	  @*/
	/*@ pure @*/ String getValue();

	/*@ requires newType == UNOConstants.NUMBERS || newType == UNOConstants.ACTION || newType == UNOConstants.WILD;
	  @*/
	void setType(int newType);

	/*@ ensures \result == UNOConstants.NUMBERS || \result == UNOConstants.ACTION || \result == UNOConstants.WILD;
	  @*/
	/*@ pure @*/ int getType();
}
