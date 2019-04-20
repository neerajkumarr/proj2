import java.io.*;

public class PosteriorMain {

    public static void main(String[] args) throws IOException {

    	PostProbability hyp_1 = new PostProbability(0.1d, 1.0d, 0.0d);
        PostProbability hyp_2 = new PostProbability(0.2d, 0.75d, 0.25d);
        PostProbability hyp_3 = new PostProbability(0.4d, 0.5d, 0.5d);
        PostProbability hyp_4 = new PostProbability(0.2d, 0.25d, 0.75d);
        PostProbability hyp_5 = new PostProbability(0.1d, 0.0d, 1.0d);

    	 String result;
        result = "result.txt";
        FileWriter file = new FileWriter(result);
        PrintWriter print = new PrintWriter(file);

        if(args.length > 2) {
            System.out.println("[Usage] java posterior <observation string>");
            System.exit(0);
        }
        if(args.length == 0) {

            try {
                print.write("Observation sequence Q = EMPTY \n");
                print.write( "Length of Q = 0\n");

                print.printf("P(hyp_1 | Q) = %.2f \n",hyp_1.p_probability);
                print.printf("P(hyp_2 | Q) = %.2f \n",hyp_2.p_probability);
                print.printf("P(hyp_3 | Q) = %.2f \n",hyp_3.p_probability);
                print.printf("P(hyp_4 | Q) = %.2f \n",hyp_4.p_probability);
                print.printf("P(hyp_5 | Q) = %.2f \n",hyp_5.p_probability);


                print.write("Probability that the next candy we pick will be C, given Q: 0.50f \n");
                print.write("Probability that the next candy we pick will be L, given Q: 0.50f");
                print.close();
            }
            catch(Exception e) {
                System.out.println("Unable to create result file");

            }
            System.exit(0);

        }

        print.printf("Observation sequence Q =  " + args[0] + "\n");
        print.printf("Length of Q = " + args[0].length() + "\n");

        double chry = 0.0d;
        double lim = 0.0d;
        double prob = 0.0d;
        for( int i = 0; i < args[0].length(); i++) {

            chry = (hyp_1.p_probability*hyp_1.cherry) + (hyp_2.p_probability*hyp_2.cherry) + (hyp_3.p_probability*hyp_3.cherry)
                    + (hyp_4.p_probability*hyp_4.cherry) + (hyp_5.p_probability*hyp_5.cherry);
            lim = (hyp_1.p_probability*hyp_1.lime) + (hyp_2.p_probability*hyp_2.lime) + (hyp_3.p_probability*hyp_3.lime)
                    + (hyp_4.p_probability*hyp_4.lime) + (hyp_5.p_probability*hyp_5.lime);

            if(args[0].charAt(i) == 'C') {
                prob = ((hyp_1.cherry * hyp_1.p_probability) / chry);
                hyp_1.p_probability = prob;
                prob = ((hyp_2.cherry * hyp_2.p_probability) / chry);
                hyp_2.p_probability = prob;
                prob = ((hyp_3.cherry * hyp_3.p_probability) / chry);
                hyp_3.p_probability = prob;
                prob = ((hyp_4.cherry * hyp_4.p_probability) / chry);
                hyp_4.p_probability = prob;
                prob = ((hyp_5.cherry * hyp_5.p_probability) / chry);
                hyp_5.p_probability = prob;
            }
            else if(args[0].charAt(i) == 'L') {
                prob = ((hyp_1.lime * hyp_1.p_probability) / lim);
                hyp_1.p_probability = prob;
                prob = ((hyp_2.lime * hyp_2.p_probability) / lim);
                hyp_2.p_probability = prob;
                prob = ((hyp_3.lime * hyp_3.p_probability) / lim);
                hyp_3.p_probability = prob;
                prob = ((hyp_4.lime * hyp_4.p_probability) / lim);
                hyp_4.p_probability = prob;
                prob = ((hyp_5.lime * hyp_5.p_probability) / lim);
                hyp_5.p_probability = prob;
            }
            else {
                System.out.println("Incorrect input : please input either C or L");
                System.exit(0);
            }

            print.println();
            print.println(" After observation " + (i+1) + " = " + args[0].substring(0, i+1));
            print.printf("\nP(hyp_1 | Q) = %.5f \n",hyp_1.p_probability);
            print.printf(" P(hyp_2 | Q) = %.5f \n",hyp_2.p_probability);
            print.printf(" P(hyp_3 | Q) = %.5f \n",hyp_3.p_probability);
            print.printf(" P(hyp_4 | Q) = %.5f \n",hyp_4.p_probability);
            print.printf(" P(hyp_5 | Q) = %.5f \n",hyp_5.p_probability);

            print.printf("\n Probability that the next candy we pick will be C, given Q: %.5f \n", chry);
            print.printf("\n Probability that the next candy we pick will be L, given Q: %.5f \n", lim);
        }

        print.close();
    }
}
