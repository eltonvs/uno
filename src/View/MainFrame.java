package View;


import javax.swing.JFrame;

import Interfaces.GameConstants;
import ServerController.Server;


public class MainFrame extends JFrame implements GameConstants {

	/*@ public initially mainPanel != null;
	  @ public invariant mainPanel != null;
	  @*/
	private /*@ spec_public nullable @*/ Session mainPanel;
	
	/*@ public initially server != null;
	  @ public invariant server != null;
	  @*/
	private /*@ spec_public nullable @*/ Server server;

	public MainFrame(){
		server = new Server();
		CARDLISTENER.setServer(server);
		BUTTONLISTENER.setServer(server);

		mainPanel = server.getSession();
		add(mainPanel);
	}
}
