package ServerController;
import java.awt.Point;
import java.awt.event.MouseAdapter;
import java.awt.event.MouseEvent;

import View.UNOCard;

public class MyCardListener extends MouseAdapter {

	private /*@ spec_public nullable @*/ UNOCard sourceCard;

	private /*@ spec_public nullable @*/ Server myServer;

	/*@ requires server != null;
	  @ assignable server;
	  @ ensures myServer == server;
	  @*/
	public void setServer(Server server){
		myServer = server;
	}

	@Override
	/*@ requires e != null;
	  @ requires myServer != null;
	  @ assignable sourceCard, myServer;
	  @ ensures sourceCard != null;
	  @ ensures myServer == \old(myServer);
	  @*/
	public void mousePressed(/*@ non_null @*/ MouseEvent e) {
		sourceCard = (UNOCard) e.getSource();

		try{
			if(myServer.canPlay)
				myServer.playThisCard(sourceCard);

		}catch(NullPointerException ex){
			ex.printStackTrace();
		}
	}

	@Override
	/*@ requires e != null;
	  @ requires myServer != null;
	  @ assignable sourceCard, myServer;
	  @ ensures sourceCard != null;
	  @ ensures myServer == \old(myServer);
	  @*/
	public void mouseEntered(/*@ non_null @*/ MouseEvent e) {
		super.mouseEntered(e);

		sourceCard = (UNOCard) e.getSource();
		Point p = sourceCard.getLocation();
		p.y -=20;
		sourceCard.setLocation(p);
	}

	@Override
	/*@ requires e != null;
	  @ requires myServer != null;
	  @ assignable sourceCard, myServer;
	  @ ensures sourceCard != null;
	  @ ensures myServer == \old(myServer);
	  @*/
	public void mouseExited(/*@ non_null @*/ MouseEvent e) {
		sourceCard = (UNOCard) e.getSource();
		Point p = sourceCard.getLocation();
		p.y +=20;
		sourceCard.setLocation(p);
	}

	@Override
	//@ assignable \nothing;
	public void mouseReleased(/*@ non_null @*/ MouseEvent e) {

	}

}
