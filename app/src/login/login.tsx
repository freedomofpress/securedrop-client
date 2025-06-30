const { the_api } = window

document.getElementById('loginButton')?.addEventListener('click', () => {
  const username = (document.getElementById('username') as HTMLInputElement).value;
  const password = (document.getElementById('password') as HTMLInputElement).value;
  const twofactor = (document.getElementById('twofactor') as HTMLInputElement).value;

  // Perform login logic (e.g., validate credentials)
  if (username === 'user' && password === 'pass' && twofactor === '123456' ) {
    the_api.send('login-success'); // Send message to main process
  } else {
    alert('Invalid credentials');
  }
});
