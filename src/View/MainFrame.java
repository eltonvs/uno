package View;


import javax.swing.JFrame;

import Interfaces.GameConstants;
import ServerController.Server;


public class MainFrame extends JFrame implements GameConstants {

	private /*@ spec_public nullable @*/ Session mainPanel;
	private /*@ spec_public nullable @*/ Server server;

	public MainFrame(){
		server = new Server();
		CARDLISTENER.setServer(server);
		BUTTONLISTENER.setServer(server);

		mainPanel = server.getSession();
		add(mainPanel);
	}
}
